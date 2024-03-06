import json
import os
from pathlib import Path

def write_to_new_json(data, directory=".", filename_prefix="data", extension=".json"):
    """
    Writes data to a new JSON file in the specified directory.
    Each call to this function will write to a different file, based on a sequence number.

    :param data: Data to be written to the JSON file.
    :param directory: Directory where the JSON file will be created. Defaults to the current directory.
    :param filename_prefix: Prefix for the filename. Defaults to 'data'.
    :param extension: File extension. Defaults to '.json'.
    """
    os.makedirs(directory, exist_ok=True)

    # Find the next sequence number not used by any file
    sequence_number = 1
    while True:
        filename = f"{filename_prefix}_{sequence_number}{extension}"
        filepath = os.path.join(directory, filename)
        if not os.path.exists(filepath):
            break
        sequence_number += 1

    with open(filepath, 'w') as json_file:
        json.dump(data, json_file, indent=4)

    # print(f"Data written to {filepath}")
    return filepath


# data = {"example": "This is some example data."}
# write_to_new_json(data)  # This will create 'data_1.json', then 'data_2.json', etc., on subsequent calls.

def load_json_as_list(file_name):
    # Load the entire JSON file, which is expected to be a list of dictionaries
    with open(file_name, 'r') as file:
        data_list = json.load(file)
    return data_list