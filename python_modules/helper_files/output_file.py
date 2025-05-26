import json
import os
class CustomJSONEncoder(json.JSONEncoder):
    """ Custom JSON encoder to handle custom objects """
    def default(self, obj):
        if hasattr(obj, 'to_dict'):
            return obj.to_dict()
        return super().default(obj)

# Function to output the results of a code generation process to a file
def output_results(output_path: str, results):
    os.makedirs(output_path, exist_ok=True)
    """ Output the results of a code generation process to a file """
    os.makedirs(output_path, exist_ok=True)
    with open(f"{output_path}/results.txt", "w", encoding="utf-8") as f:
        f.write(json.dumps(results, indent=4, cls=CustomJSONEncoder))
