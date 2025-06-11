import json
import os

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

# Load times from E-Graph file
def load_egraph_data(filename) -> dict:
    with open(filename, 'r') as f:
        data = json.load(f)


    return data