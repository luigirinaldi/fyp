# Alive Parametric Bitwidth benchmarks

This folder contains scripts to generate parametric bitwidth benchmarks for this tools based on the benchmarks found in the artifact of 'Towards Satisfiability Modulo Parametric Bit-vectors': https://cvc4.github.io/papers/cade2019-jar.

In order to generate the benchmarks, the `bv_to_bool_bench.tar.gz` file is required and it has to be extracted into the corresponding `bv_to_bool_bench` directory inside of this directory. 

Install dependencies using `requirements.txt` and then run `python filter_queries.py ./filter.txt'

This will generate the following:
- `filtered_values` folder containing the smt queries filtered using the `filter.txt` file from the artifact as well as by selecting only those queries that contain `BitVec 4` as was done in the artifact. 
- `valid_queries`, a folder containing those queries that can be translated into `bw_lang`
- `../test_data/alive.json`, a file containing the transformed parametric bitvector queries in `bw_lang` 