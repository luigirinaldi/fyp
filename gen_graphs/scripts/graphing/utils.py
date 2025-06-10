import json

# Load times from E-Graph file
def load_egraph_data(filename) -> dict:
    with open(filename, 'r') as f:
        data = json.load(f)


    return data