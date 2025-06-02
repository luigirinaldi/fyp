#!/bin/sh

mkdir -p ./processed_artifact

for item in ./cluster_results_alive/*; do python parse_artifact_results.py "$item" "./processed_artifact/$(basename $item).json"; done;