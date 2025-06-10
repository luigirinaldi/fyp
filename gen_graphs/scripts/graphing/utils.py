import json

# Load times from E-Graph file
def load_egraph_data(filename) -> dict:
    with open(filename, 'r') as f:
        data = json.load(f)

    return {theorem: float(entry['summary']['total_time']) for theorem, entry in data.items() if entry['summary']['stop_reason'] == {"Other":"Found equivalence"}}
