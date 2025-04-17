""" This is the main file for the tool. It contains the main function that is called 
    when the tool is run. It also contains the functions that are called based on the 
    arguments given to the tool. """
import os
import argparse
from dotenv import load_dotenv
from python_modules.helper_files.list_files import list_files_directory
from python_modules.LLM.pipeline import generate_specification_process

# Function that generates a specification in a folder
def generate_specification_folder(directory: str, output_path: str, model_name: str, iterations: int, temperature: float, initial_examples_generated: int, temp_folder: str):
    # Get the folders in the directory
    files_folder = list_files_directory(directory)

    # filter on C files that have the c file
    c_files_folder = [folder for folder in files_folder if folder.endswith(".c")]

    # For each C file in the folder
    for c_file in c_files_folder:
        # Get the C file
        c_file_path = os.path.join(directory, c_file)
        
        print(f"Starting to generate code for file {c_file}....")

        # Set the output path
        output_file = f"{output_path}/{model_name}_{c_file.replace('.c', '.txt')}"

        # Create an output directory for all the files if it does not exist yet
        if not os.path.exists(output_path):
            os.mkdir(output_path)

        # Generate the specification
        generate_specification_process(c_file_path, output_file, model_name, iterations, temperature, initial_examples_generated, temp_folder)

        # Print the current generated file
        print("\n \n" + "-" * 100 + "\n \n")
        print(f"Generated Specification for file {c_file}. \n\n")

def parse_arguments():
    """Parse the arguments given to the tool"""
    # Create argument parser
    parser = argparse.ArgumentParser()

    # Arguments related to I/O
    parser.add_argument("-d", "--directory", help="The directory to use for verification of the files.", type=str, default=os.path.join(os.getcwd(), "input"))
    parser.add_argument('-o', '--output_path', help="The output path to use for the code \
                        generation", type=str, default=os.path.join(os.getcwd(), "output"))
    parser.add_argument("-tmp", "--temp_folder", help="The folder where temporary files are stored", default= os.path.join(os.getcwd(), "..", "tmp"), type=str)    # Arguments for Debugging

    # Tool arguments
    parser.add_argument("-iter", "--iterations", help="The number of iterations to use for \
                        the code generation", type=int, default=3)
    parser.add_argument('-temp', '--temperature', help="The temperature to use for the code \
                        generation", type=float, default=1)
    parser.add_argument('-model', '--model_name', help="The model name to use for the \
                        code generation", type=str, default="gpt-4o-mini")
    parser.add_argument("-ieg", "--initial_examples_generated", help="The amount of initial examples that are generated for each problem", default=1, type=int)

    # Parse arguments
    return parser.parse_args()

# Main function
if __name__ == "__main__":
    # Load the environment variables
    load_dotenv()

    # Get a list of the functions
    arguments = parse_arguments()

    # Get the function from switcher dictionary
    generate_specification_folder(arguments.directory, arguments.output_path, arguments.model_name, arguments.iterations, arguments.temperature, arguments.initial_examples_generated, arguments.temp_folder)

