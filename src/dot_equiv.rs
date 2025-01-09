/*!
EGraph visualization with [GraphViz]

Custom Dot implementatation to display common nodes between two potentially equivalent expressions
*/

use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::io::{Error, ErrorKind, Result, Write};
use std::path::Path;

use egg::*;

pub struct DotEquiv<'a, L: Language, N: Analysis<L>> {
    pub egraph: &'a EGraph<L, N>,
    pub lhs: &'a RecExpr<L>,
    pub rhs: &'a RecExpr<L>,
    /// A list of strings to be output top part of the dot file.
    pub config: Vec<String>,
    /// Whether or not to anchor the edges in the output.
    /// True by default.
    pub use_anchors: bool,
}

impl<'a, L, N> DotEquiv<'a, L, N>
where
    L: Language + Display,
    N: Analysis<L>,
{
    /// Writes the `Dot` to a .dot file with the given filename.
    /// Does _not_ require a `dot` binary.
    pub fn to_dot(&self, filename: impl AsRef<Path>) -> Result<()> {
        let mut file = std::fs::File::create(filename)?;
        write!(file, "{}", self)
    }

    /// Adds a line to the dot output.
    /// Indentation and a newline will be added automatically.
    pub fn with_config_line(mut self, line: impl Into<String>) -> Self {
        self.config.push(line.into());
        self
    }

    /// Set whether or not to anchor the edges in the output.
    pub fn with_anchors(mut self, use_anchors: bool) -> Self {
        self.use_anchors = use_anchors;
        self
    }

    /// Renders the `Dot` to a .png file with the given filename.
    /// Requires a `dot` binary to be on your `$PATH`.
    pub fn to_png(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tpng".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    /// Renders the `Dot` to a .svg file with the given filename.
    /// Requires a `dot` binary to be on your `$PATH`.
    pub fn to_svg(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&[
            "-Tsvg".as_ref(),
            "-o".as_ref(),
            filename.as_ref(),
            "-q".as_ref(),
        ])
    }

    /// Renders the `Dot` to a .pdf file with the given filename.
    /// Requires a `dot` binary to be on your `$PATH`.
    pub fn to_pdf(&self, filename: impl AsRef<Path>) -> Result<()> {
        self.run_dot(&["-Tpdf".as_ref(), "-o".as_ref(), filename.as_ref()])
    }

    /// Invokes `dot` with the given arguments, piping this formatted
    /// `Dot` into stdin.
    pub fn run_dot<S, I>(&self, args: I) -> Result<()>
    where
        S: AsRef<OsStr>,
        I: IntoIterator<Item = S>,
    {
        self.run("dot", args)
    }

    /// Invokes some program with the given arguments, piping this
    /// formatted `Dot` into stdin.
    ///
    /// Can be used to run a different binary than `dot`:
    /// ```no_run
    /// # use egg::*;
    /// # let mut egraph: EGraph<SymbolLang, ()> = Default::default();
    /// egraph.dot().run(
    ///     "/path/to/my/dot",
    ///     &["arg1", "-o", "outfile"]
    /// ).unwrap();
    /// ```
    pub fn run<S1, S2, I>(&self, program: S1, args: I) -> Result<()>
    where
        S1: AsRef<OsStr>,
        S2: AsRef<OsStr>,
        I: IntoIterator<Item = S2>,
    {
        use std::process::{Command, Stdio};
        let mut child = Command::new(program)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()?;
        let stdin = child.stdin.as_mut().expect("Failed to open stdin");
        write!(stdin, "{}", self)?;
        match child.wait()?.code() {
            Some(0) => Ok(()),
            Some(e) => Err(Error::new(
                ErrorKind::Other,
                format!("dot program returned error code {}", e),
            )),
            None => Err(Error::new(
                ErrorKind::Other,
                "dot program was killed by a signal",
            )),
        }
    }

    // gives back the appropriate label and anchor
    fn edge(&self, i: usize, len: usize) -> (String, String) {
        assert!(i < len);
        let s = |s: &str| s.to_string();
        if !self.use_anchors {
            return (s(""), format!("label={}", i));
        }
        match (len, i) {
            (1, 0) => (s(""), s("")),
            (2, 0) => (s(":sw"), s("")),
            (2, 1) => (s(":se"), s("")),
            (3, 0) => (s(":sw"), s("")),
            (3, 1) => (s(":s"), s("")),
            (3, 2) => (s(":se"), s("")),
            (_, _) => (s(""), format!("label={}", i)),
        }
    }
}

impl<'a, L: Language, N: Analysis<L>> Debug for DotEquiv<'a, L, N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_tuple("Dot").field(self.egraph).finish()
    }
}

fn get_classes_from_root<L: Language, N: Analysis<L>>(
    egraph: &EGraph<L, N>,
    root_expr: &RecExpr<L>,
) -> HashMap<Id, bool> {
    let mut id_map: HashMap<_, _> = egraph
        .classes()
        .into_iter()
        .map(|class| (class.id, (class, false)))
        .collect();

    let root_id = egraph.lookup_expr(root_expr).unwrap();

    let mut worklist = vec![root_id];

    while worklist.len() > 0 {
        let curr_id = worklist.pop().unwrap();

        if let Some((curr_class, is_set)) = id_map.get_mut(&curr_id) {
            if !*is_set {
                *is_set = true;
                for node in curr_class.iter() {
                    node.for_each(|child_id| worklist.push(child_id));
                }
            }
        }
    }

    return id_map
        .iter()
        .map(|(id, (_class, in_expr))| (*id, *in_expr))
        .collect();
}

impl<'a, L, N> Display for DotEquiv<'a, L, N>
where
    L: Language + Display,
    N: Analysis<L>,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "digraph egraph {{")?;
        let lhs_colour = "cyan";
        let rhs_colour = "yellow";
        let both_colour = "chartreuse";

        // set compound=true to enable edges to clusters
        writeln!(f, "  compound=true")?;
        writeln!(f, "  clusterrank=local")?;

        for line in &self.config {
            writeln!(f, "  {}", line)?;
        }

        let lhs_map = get_classes_from_root(self.egraph, self.lhs);
        let rhs_map = get_classes_from_root(self.egraph, self.rhs);

        // define all the nodes, clustered by eclass
        for class in self.egraph.classes() {
            writeln!(f, "  subgraph cluster_{} {{", class.id)?;
            writeln!(f, "    style=dotted")?;

            let colour = match (lhs_map.get(&class.id), rhs_map.get(&class.id)) {
                (Some(true), Some(true)) => both_colour,
                (Some(true), Some(false)) => lhs_colour,
                (Some(false), Some(true)) => rhs_colour,
                (Some(false), Some(false)) => "gray",
                _ => {
                    println!("Something has gone horribly wrong");
                    "black"
                }
            };

            for (i, node) in class.iter().enumerate() {
                writeln!(
                    f,
                    "    {}.{}[label = \"{}\", style=filled, fillcolor = \"{}\"]",
                    class.id, i, node, colour
                )?;
            }
            writeln!(f, "  }}")?;
        }

        for class in self.egraph.classes() {
            for (i_in_class, node) in class.iter().enumerate() {
                let mut arg_i = 0;
                node.try_for_each(|child| {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let (anchor, label) = self.edge(arg_i, node.len());
                    let child_leader = self.egraph.find(child);

                    if child_leader == class.id {
                        writeln!(
                            f,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{}{} -> {}.{}:n [lhead = cluster_{}, {}]",
                            class.id, i_in_class, anchor, class.id, i_in_class, class.id, label
                        )?;
                    } else {
                        writeln!(
                            f,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{}{} -> {}.0 [lhead = cluster_{}, {}]",
                            class.id, i_in_class, anchor, child, child_leader, label
                        )?;
                    }
                    arg_i += 1;
                    Ok(())
                })?;
            }
        }

        write!(f, "}}")
    }
}

pub fn make_dot<'a, L: Language, N: Analysis<L>>(
    egraph: &'a EGraph<L, N>,
    lhs: &'a RecExpr<L>,
    rhs: &'a RecExpr<L>,
) -> DotEquiv<'a, L, N> {
    DotEquiv {
        egraph,
        lhs,
        rhs,
        config: vec![],
        use_anchors: true,
    }
}
