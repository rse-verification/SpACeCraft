""" This module contains the function that iteratively generates a prompt based on a 
    verification error message """
from python_modules.LLM.code_generation_objects import IterationInformation, CompletionInformation, SpecificationGenerationProcess
from python_modules.helper_files.output_file import output_results
from python_modules.LLM.llm_module import format_prompt, initialize_llms, prompt_with_temp
from python_modules.Verify_files.verify_file import initialize_solvers
from python_modules.Verify_files.check_file import check_file
import os

# Initialize the LLMs and solvers
llm_models = initialize_llms()
solvers = initialize_solvers()
normalized_solvers = ",".join(s.lower() for s in solvers)

def generate_specification_process(c_code: str, output_path: str, model_name: str, iterations: int, temperature: float, initial_examples_generated: int, temp_folder: str):
    """Function to iteratively generate specification and check it
    Returns:
        specification_generati  on_process: The specification generation process
    Args:
        c_code: The C code to use for the initial specification generation
        output_path: The path to the output file
        model_name: The name of the model to use
        iterations: The number of iterations to run
        temperature: The temperature to use for the initial specification generation
        initial_examples_generated: The number of initial examples to generate
        temp_folder: The path to the temporary folder   
    """

    # Create a specification generation process object
    specification_generation_process = SpecificationGenerationProcess(iterations)


    print("-" * 50)
    print(f"Initial specification generation.")
    # Perform the initial specification generation step
    initial_specification_generation_information = initial_specification_generation_step(c_code, initial_examples_generated, model_name, temperature, temp_folder, output_path)

    # Add the initial specification generation information to the specification generation process
    specification_generation_process.add_initial_specification_generation_information(initial_specification_generation_information)

    verified = initial_specification_generation_information.is_verified

    # Create an index for the specification improvement iterations
    i = 0
    last_iteration = initial_specification_generation_information
    # Do the specification improvement steps until the specification is verified or the maximum iterations are reached
    while (i < iterations and not verified):
        print("    " + "-" * 50)
        print(f"    specification improvement iteration {i + 1} of {iterations}.")
        print("    " + "-" * 50)

         # Take the best attempt from the initial generation attempts
        code = last_iteration.best_attempt_specification
        output = last_iteration.best_attempt_feedback

        # Perform the specification improvement step
        specification_improvement_information = specification_improvement_step(i, code, output, initial_examples_generated, model_name, temperature, temp_folder, output_path)
        
        # Add the specification improvement information to the specification generation process
        specification_generation_process.add_specification_improvement_information(specification_improvement_information)

        # Stop if the specification is verified
        verified = specification_improvement_information.is_verified

        # Update the last iteration and the counter
        last_iteration = specification_improvement_information
        i += 1

    # Print the results
    print(f"    Total completions used: {specification_generation_process.total_completions_used} total time taken: {specification_generation_process.total_time_taken_verification}.")
    print(f"    Has the specification been successfully verified: {verified}")

    # save the results to a file
    output_results(output_path, specification_generation_process.to_dict())
    return specification_generation_process

# Function for initial specification generation
def initial_specification_generation_step(c_code: str, initial_examples_generated: int, model_name: str, temperature: float, temp_folder: str, output_path: str):
    """Function to generate the initial specification based on the arguments
    Args:
        c_code: The C code to use for the initial specification generation
        initial_examples_generated: The number of initial examples to generate
        model_name: The name of the model to use
        temperature: The temperature to use for the initial specification generation
        temp_folder: The temporary folder to store the compiled file
        output_path: The path to the output file
    Returns:
        responses_gpt: The responses from the LLM
        tokens_used: The amount of tokens used for each response
        model_used: The model used, no list is used as only one model is used
    """

    # Information related to the iterations
    iteration_info = IterationInformation(0, initial_examples_generated)

    # For each initial attempt, get the response, tokens used, and model used
    for llm_response_index in range(initial_examples_generated):
        print("    " + ("-" * 50))
        print(f"    Initial specification generation, specification completion {llm_response_index + 1} of {initial_examples_generated}.")
        print("    " + ("-" * 50))

        # Read the c code
        with open(c_code, "r", encoding="utf-8") as f:
            c_code_content = f.read()

        # Get the output path
        filled_prompt = format_prompt("initial_prompt", c_code_content)

        # generate the initial attempts by making prompts of at most x each
        llm_response = prompt_with_temp(llm_models[model_name], filled_prompt, temperature=temperature)

        # Process the generated specification and get information about the completion
        completion_information = process_specification_and_get_completion_information(llm_response, 0, filled_prompt, temperature, temp_folder, output_path, initial_attempt = True)

        # Add the completion to the iteration information
        iteration_info.add_completion(completion_information)

        # If the specification is verified, then stop
        if completion_information.is_verified:
            break

    return iteration_info

# Function that performs one iteration of specification improvement
def specification_improvement_step(
    iteration_number: int,
    code: str,
    feedback: str,
    num_attempts: int,
    model_name: str,
    temperature: float,
    temp_folder: str,
    output_path: str,
) -> IterationInformation:
    """
    Perform one iteration of specification improvement based on an existing spec and
    its verification feedback.
    Args:
        iteration_number: which improvement iteration this is (1-based)
        code: the previous best specification (C code)
        feedback: the verification error/output for that code
        num_attempts: how many alternative repairs to try
        model_name: which LLM model to use
        temperature: sampling temperature
        temp_folder: where to compile/verify temporary files
        output_path: where to write the repaired .c files
    Returns:
        iteration_info: an IterationInformation containing all attempts
    """
    iteration_info = IterationInformation(iteration_number, num_attempts)

    # Build the repair prompt once
    filled_prompt = format_prompt("repair_prompt", code, feedback)

    for attempt_idx in range(num_attempts):
        print("-" * 50)
        print(f"    Improvement Iteration {iteration_number + 1}, attempt {attempt_idx + 1} of {num_attempts}")
        print("-" * 50)

        # Ask the LLM for a repair
        llm_response = prompt_with_temp(
            llm_models[model_name],
            filled_prompt,
            temperature=temperature
        )

        # Process and verify this candidate
        completion_info = process_specification_and_get_completion_information(
            response_gpt=llm_response,
            i=iteration_number,
            prompt=filled_prompt,
            temperature=temperature,
            temp_folder=temp_folder,
            output_path=output_path,
            initial_attempt=False
        )

        iteration_info.add_completion(completion_info)

        # Stop early if it verifies
        if completion_info.is_verified:
            break

    return iteration_info

# Function that processes the specification, and gets iteration information, and verifies the goals
def process_specification_and_get_completion_information(response_gpt, i, prompt, temperature, temp_folder: str, output_path: str, initial_attempt = False):
    """Function to process the generated specification and get iteration information
    Args:
        response_gpt: The response from the GPT model
        i: The iteration number
        prompt: The prompt that has been used
        temperature: The temperature used
        temp_folder: The temporary folder to store the compiled file
        output_path: The path to the output file
        initial_attempt: Boolean that indicates if this is the initial attempt
        output_path: The output path of the file
    Returns:
        completion_information: The information about the completion
    """

    # Process the generated specification
    # Extract the code from the response,
    code = parse_llm_output(response_gpt)

    # Save the response to a file
    absolute_c_path = os.path.abspath(output_path) + f"/initial_response_{i}.c"

    # Create the output directory if it does not exist
    os.makedirs(output_path, exist_ok=True)
    with open(absolute_c_path, "w", encoding="utf-8") as f:
        f.write(code)

    verified, verification_output, verified_goals, verification_time_taken = check_file(absolute_c_path, temp_folder, normalized_solvers)
                                                                       
     # Add extra information about the generation attempt
    if initial_attempt:
        information = "Initial specification generation attempt"
    elif verified:
        information = "The code and specification has been verified"
    else:
        information = "The specificationhas been improved"

    # Create an object that will contain information about the completion
    completion_information = CompletionInformation(i, prompt, code,  verified, verified_goals, temperature ,information, code, verification_output, verification_time_taken)

    return completion_information


def parse_llm_output(output_llm):
    """
    Parses the output of the LLM and returns the code and specification generated by the LLM.
    This is done by looking at the <code> and </code> tags or ```c and ``` tags in the output.
    The language identifier is matched case-insensitively.
    """
    text = output_llm.text()
    # Case-insensitive check for <code> tags
    if "<code>" in text.lower() and "</code>" in text.lower():
        start_index = text.lower().find("<code>") + len("<code>")
        end_index = text.lower().find("</code>")
        code_block = text[start_index:end_index].strip()
        return code_block

    # Case-insensitive check for ```c blocks
    lowered_text = text.lower()
    if "```c" in lowered_text:
        start_index = lowered_text.find("```c") + len("```c")
        end_index = lowered_text.find("```", start_index)
        if end_index != -1:
            code_block = text[start_index:end_index].strip()
            return code_block

    return text
