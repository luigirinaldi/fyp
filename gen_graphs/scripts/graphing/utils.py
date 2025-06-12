import json
import os
import pandas as pd

def get_egraph_from_dir(data_dir = "../../data/"):
    data_dir = "../../data/"

    egraph_data = {}

    for direc in os.listdir(data_dir):
        try:
            egraph_data[direc] = (
            load_egraph_data(f"{data_dir}{direc}/egraph_stats.json"),
            load_egraph_data(f"{data_dir}{direc}/egraph_stats_mem.json"),
        )
        except:
            continue

    return egraph_data

def format_bytes(size_bytes: int) -> str:
    """Convert bytes to a human-readable format (e.g., KB, MB, GB)."""
    # if size_bytes == 0:
    #     return "0B"
    # units = ("B", "KB", "MB", "GB", "TB", "PB", "EB", "ZB", "YB")
    # power = 2 ** 10  # 1024 (binary system)
    # for unit in units:
    #     if size_bytes < power:
    #         return f"{size_bytes:.0f} {unit}"
    #     size_bytes /= power
    # return f"{size_bytes:.2f} YB"  # Fallback (unlikely)
    # convert to MB
    return f"{size_bytes / 2**20:.2f}"

def parse_stop(stop):
    match stop:
        case "Saturated":
            return "Saturated"
        case {"Other": "Found equivalence"}:
            return "Equivalent"
        case {"TimeLimit": _limit}:
            return "Timeout"
        case {"NodeLimit": _limit}:
            return "NodeLimit"
        case err:
            raise NotImplementedError(f"This shouldn't happen {err}")

def get_dataframes(egraph_data):
    dataframes = {}

    for test_set, (data, data_mem) in egraph_data.items():
        processed = {theorem: entry["summary"] for theorem, entry in data.items()}
        for theorem, info in data_mem.items():
            processed[theorem]["memory"] = format_bytes(int(info["memory_footprint"]))
        for theorem, info in data.items():
            # use the crude time since it feels more correct, also convert to milliseconds
            processed[theorem]["runtime"] = info["crude_time"] * 1000
        df = pd.DataFrame(processed)
        df = df.transpose()
        df["stop_reason"] = df["stop_reason"].map(parse_stop)

        df = df.sort_values(by=["stop_reason", "total_time"])

        dataframes[test_set] = df
    return dataframes

def load_sledge_data(filename):
    with open(filename, 'r') as f:
        data = json.load(f)

    times = {}
    for theorem, entry in data.items():
        if (meth:=entry['method']) != 'timeout':
            if meth == 'cvc5':
                times[theorem] = entry['atp_time']
            else:
                raise NotImplementedError('not supporting other solver yet')
        else:
            times[theorem] = None
    return times

# Load times from E-Graph file
def load_egraph_data(filename) -> dict:
    with open(filename, 'r') as f:
        data = json.load(f)


    return data


def prepare_step_data(series):
    times = sorted(series)
    x = [0]
    y = [0]
    for i, t in enumerate(times, start=1):
        x.extend([t, t])
        y.extend([y[-1], i])
    return x, y