""" This is the main file for the tool. It contains the main function that is called 
    when the tool is run. It also contains the functions that are called based on the 
    arguments given to the tool. """
import os
import argparse
from dotenv import load_dotenv
from python_modules.LLM.experiment_parameters import initialize_llms
from python_modules.LLM.verify import initialize_solvers

def generate_specification(args):
    """Generate a specification for a given C file"""
    print("Generating specification for the given C file")

    # Get the code from the c file
    with open(args.absolute_c_path, "r", encoding="utf-8") as f:
        code = f.read()

    # Generate the specification
    specification = generate_specification(code)

def parse_arguments():
    """Parse the arguments given to the tool"""
    # Create argument parser
    parser = argparse.ArgumentParser()

    # Arguments related to I/O
    parser.add_argument("-d", "--directory", help="The directory to use for verification of the files.", type=str)
    parser.add_argument("-c", "--c_file", help="The C file to use", type=str)
    parser.add_argument('-o', '--output_path', help="The output path to use for the code \
                        generation", type=str)
    parser.add_argument('-output-file', '--output_file_name', help="The output file to use for the \
                        code generation", type=str)
    parser.add_argument("-tmp", "--temp_folder", help="The folder where temporary files are stored", default= os.path.join(os.getcwd(), "..", "tmp"), type=str)    # Arguments for Debugging

   # Verification arguments
    parser.add_argument("-wpt", "--wp_timeout", help="The timeout to use for the wp-prover",
                        type=int, default=2)
    parser.add_argument("-wps", "--wp_steps", help="The steps to use for the wp-prover",
                        type=int, default=1500000)
    parser.add_argument("-s", "--solver", help="The solver to use for the formal verification",
                        type=str)
    parser.add_argument("-sd", "--smoke_detector", help="The smoke detector to use for the \
                        formal verification", type=bool, action=argparse.BooleanOptionalAction,
                        default=True)

    # Tool arguments
    parser.add_argument("-iter", "--iterations", help="The number of iterations to use for \
                        the code generation", type=int, default=10)
    parser.add_argument('-temp', '--temperature', help="The temperature to use for the code \
                        generation", type=float, default=1)
    parser.add_argument('-model', '--model_name', help="The model name to use for the \
                        code generation", type=str, default="gpt-3.5-turbo")
    parser.add_argument("-ieg", "--initial_examples_generated", help="The amount of initial examples that are generated for each problem", default=10, type=int)

    # Parse arguments
    return parser.parse_args()

# Main function
if __name__ == "__main__":
    # Load the environment variables
    load_dotenv()

    # Initialize the LLMs and solvers
    llm_models = initialize_llms()
    solvers = initialize_solvers()


    # Get a list of the functions
    arguments = parse_arguments()

    # Ensure that the integers are valid
    ensure_integers(arguments)

    # Clear the debugging folders if the clear argument is given
    if arguments.clear:
        clear(arguments)

    # Get the function from switcher dictionary
    generate_specification(arguments)