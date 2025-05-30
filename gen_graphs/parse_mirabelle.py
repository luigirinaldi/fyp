import re
import sys
import json
from pprint import pprint


def parse_log_file(filename):
    results = {}

    with open(filename, "r") as file:
        for i, line in enumerate(file):
            if sledge_match := re.match(
                r".*sledgehammer goal\.proof\s*(\d+)ms .*LemmaSledge\.([a-zA-Z_0-9]+) \d+:\d+.*((.*(some)(.*))|.*(timeout).*)",
                line,
            ):
                name = sledge_match.group(2)
                total_time = int(sledge_match.group(1))
                if sledge_match.group(5) == "some":
                    proof_info = sledge_match.group(3)
                    if match := re.match(
                        r".*\(SH (\d+)ms, ATP (\d+)ms\) \[cvc4\].*Try this:(.*)",
                        proof_info,
                    ):
                        info = {
                            "method": "cvc4",
                            "total_time": total_time,
                            "sh_time": int(match.group(1)),
                            "atp_time": int(match.group(2)),
                            "proof": match.group(3).strip(),
                        }
                    else:
                        info = {
                            "method": "unknown",
                            "total_time": total_time,
                            "proof": proof_info.strip(),
                        }
                    results.setdefault(name, []).append(info)
                elif sledge_match.group(7) == "timeout":
                    results.setdefault(name, []).append(
                        {"method": "timeout", "total_time": total_time}
                    )
    return results


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python script.py <log_file_path> <output_json_path>")
        sys.exit(1)

    log_path = sys.argv[1]
    output_path = sys.argv[2]

    parsed_results = parse_log_file(log_path)

    timeouts = [k for k, v in parsed_results.items() if v[0]["method"] == "timeout"]
    print("Found", len(parsed_results), "theorems.", len(timeouts), "timeouts:\n  ", " ".join(timeouts))

    output_dict = {}

    for k, v in parsed_results.items():
        if any(x["method"] == "timeout" for x in v):
            assert len(v) == 1, f"More than one timeout parsed for {k}:\n{v}"
            output_dict[k] = v[0]
        elif any(poses := [x["method"] == "cvc4" for x in v]):
            out_val = v.pop(poses.index(True))
            assert all(x["method"] != "cvc4" for x in v), (
                f"There are other cvc4 proofs for {k}:\n{v}"
            )
            output_dict[k] = out_val

    # pprint(output_dict)

    with open(output_path, "w") as out_file:
        json.dump(output_dict, out_file, indent=2)
