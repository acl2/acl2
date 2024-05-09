import sys
import os.path
import pathlib
import json
import argparse
import re
import logging

def print_data(data):
    for key in sorted(data.keys()):
        count = sum(data[key].values())
        print(key, count)
        objects = sorted(list(data[key].items()), key=lambda x: -x[1])
        for obj, cnt in objects[:5]:
            print("    ", obj, cnt)

def process_file(fname, data):
    if os.path.isdir(fname):
        logging.info(">>> " + fname)
        for filename in sorted(os.listdir(fname)):
            if filename.startswith('.'):
                continue
            f = os.path.join(fname, filename)
            process_file(f, data)
        return data

    if not str(pathlib.Path(fname)).endswith("mli"):
        return data

    logging.info("> " + fname)
    with open(fname, encoding='latin-1') as f:
        content = json.load(f)
        for item in content:
            action_type = item["output"]["action-type"]
            action_obj = item["output"]["action-obj"]
            if action_type not in data:
                data[action_type] = {}
            if action_obj not in data[action_type]:
                data[action_type][action_obj] = 0
            data[action_type][action_obj] += 1
    return data

if __name__ == "__main__":
    # logging.basicConfig(level=logging.DEBUG, filename='example.log', encoding='utf-8')
    logging.basicConfig(level=logging.DEBUG)
    sys.setrecursionlimit(1500)

    for fname in sys.argv:
        data = {}
        process_file(fname, data)
        print_data(data)
