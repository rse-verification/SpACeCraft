import re
import time
import subprocess
from typing import List, Tuple, Dict
from pipeline_modules.subprocess_creator import run_command

def verify_c_file(
    c_file_path: str,
    solvers: List[str],
    wp_steps: int,
    wp_timeout: int,
    smoke_tests: bool,
    timeout: int = 600
) -> Dict[str, object]:
    """
    Verifies a C file using Frama-C.
    
    Args:
        c_file_path (str): Absolute path to the C source file.
        solvers (List[str]): A list of solvers that are used for verification.
        wp_steps (int): Number of steps for WP plugin.
        wp_timeout (int): Timeout value for WP plugin.
        smoke_tests (bool): Whether to enable smoke tests.
        timeout (int, optional): Timeout for the command execution. Defaults to 600 seconds.

    Returns:
        Dict[str, object]:
            - "success" (bool): Verification success status.
            - "message" (str): Error cause or success message.
            - "goals_ratio" (str): Verified goals ratio.
            - "elapsed_time" (float): Verification time in seconds.
    """
    # Parse the solvers array 
    solvers_string = ",".join(solvers)
    
    frama_c_command = (
        f"frama-c -wp -wp-rte -wp-model real '{c_file_path}' -wp-status "
        f"-wp-prover {solvers_string} "
        f"-wp-steps {wp_steps} "
        f"-wp-timeout {wp_timeout} "
        f"{'-wp-smoke-tests ' if smoke_tests else ''}".strip()
    )
    
    stdout_str, stderr_str, completed = run_command(frama_c_command, timeout)

    if not completed:
        return {
            "verify_success": False,
            "verify_message": "Timeout",
            "verify_goals_ratio": "0 / 0",
        }
    
    return analyze_verification_output(stdout_str, c_file_path)

def analyze_verification_output(output: str, c_file_path: str) -> Dict[str, object]:
    """
    Analyzes the output from Frama-C verification.
    
    Args:
        output (str): Output from Frama-C.
        c_file_path (str): Absolute path of the C file.
        elapsed_time (float): Time taken for verification.

    Returns:
        Dict[str, object]:
            - "success" (bool): Verification success status.
            - "message" (str): Error cause or success message.
            - "goals_ratio" (str): Verified goals ratio.
            - "elapsed_time" (float): Verification time in seconds.
    """
    if "Syntax error" in output or "invalid user input" in output:
        output = re.sub(r'\[kernel\].*?\n', '', output)
        return {
            "verify_success": False,
            "verify_message": f"Syntax error detected:\n{output}",
            "verify_goals_ratio": "0 / 0",
        }
    
    if "fatal error" in output:
        return {
            "verify_success": False,
            "verify_message": f"Fatal error detected:\n{output}",
            "verify_goals_ratio": "0 / 0",
        }
    
    if "Timeout" in output:
        verified_goals, total_goals = extract_verified_goals(output)
        timeout_details = extract_timeout_details(output, c_file_path)
        return {
            "verify_success": False,
            "verify_message": timeout_details,
            "verify_goals_ratio": f"{verified_goals} / {total_goals}",
        }
    
    verified_goals, total_goals = extract_verified_goals(output)
    success = verified_goals == total_goals
    
    if success:
        print("Verification succeeded.")

    return {
        "verify_success": success,
        "verify_message": "             Verification succeeded." if success else "          Verification failed.",
        "verify_goals_ratio": f"{verified_goals} / {total_goals}",
    }

def extract_verified_goals(output: str) -> tuple:
    """Extracts the number of verified goals from Frama-C output."""
    try:
        verified_goals = output.split("Proved goals:")[1].split("/")[0].strip()
        total_goals = output.split("Proved goals:")[1].split("/")[1].strip().split("\n")[0].strip()
        return verified_goals, total_goals
    except IndexError:
        return "0", "0"

def extract_timeout_details(output: str, c_file_path: str) -> str:
    """Extracts details about timeouts from Frama-C output."""
    timeout_string = "Verification timed out. The following lines caused timeouts:\n"
    for line in output.split("\n"):
        if "Goal" in line and "(file " in line:
            line_number_match = re.search(r'line\s+(\d+)', line)
            if line_number_match:
                line_number = int(line_number_match.group(1))
                code_line = get_line_number_in_parsed_code(c_file_path, line_number)
                timeout_string += f"{line.split('(')[0]} does not hold: {code_line}\n"
    return timeout_string.strip()

def run_frama_c_print(c_file_path: str, debug: bool = False) -> str:
    """
    Runs `frama-c -print` on a C file and returns the parsed output as a string.
    
    Args:
        c_file_path (str): Path to the original C file.
        debug (bool): If True, enables debugging prints.
    
    Returns:
        str: Parsed C code output from Frama-C.
    """
    command = ["frama-c", "-print", c_file_path]
    
    if debug:
        print(f"Running command: {' '.join(command)}")
    
    try:
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
        
        if debug:
            print("Frama-C output successfully retrieved.")
        
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error running Frama-C: {e.stderr}")
        return ""
    except FileNotFoundError:
        print("Error: Frama-C is not installed or not found in PATH.")
        return ""

def get_line_number_in_parsed_code(c_file_path: str, line_number: int, debug: bool = False) -> str:
    """
    Retrieves a specific line from the parsed version of a C file using Frama-C -print.
    
    Args:
        c_file_path (str): The path to the C file to parse.
        line_number (int): The line number to retrieve.
        debug (bool): If True, enables debugging prints.
    
    Returns:
        str: The corresponding line of code in the parsed C file.
    """
    parsed_code = run_frama_c_print(c_file_path, debug)
    
    if not parsed_code:
        return ""
    
    parsed_code_lines = parsed_code.split("\n")
    
    if line_number < 1 or line_number > len(parsed_code_lines):
        print(f"Warning: Line number {line_number} is out of range for {c_file_path}.")
        return ""
    
    line = parsed_code_lines[line_number - 1].strip()
    
    if debug:
        print(f"Retrieved line {line_number} from parsed output: {line}")
    
    return line

def initialize_solvers() -> List[str]:
    """
    Retrieves the list of solvers available in Why3.
    
    Returns:
        List[str]: A list of solver names available in Why3.
    """
    try:
        # Run the Why3 solver detection command
        result = subprocess.run(
            ["why3", "config", "detect"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=True
        )
        
        # Extract lines from the output
        output_lines = result.stdout.split("\n")
        
        if len(output_lines) < 2:
            raise RuntimeError("Unexpected Why3 output format.")
        
        # Extract solvers file path from the second last line
        solvers_path = output_lines[-2].partition("/")[1] + output_lines[-2].partition("/")[2]
        
        return parse_solvers_from_file(solvers_path)
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print(f"Error executing Why3 command: {e}")
        return []

def parse_solvers_from_file(file_path: str) -> List[str]:
    """
    Parses the solvers configuration file to extract solver names.
    
    Args:
        file_path (str): Path to the Why3 solvers configuration file.
    
    Returns:
        List[str]: A list of solver names.
    """
    solver_names = []
    try:
        with open(file_path, "r", encoding="utf-8") as file:
            solvers_list = file.read().split("[partial_prover]")[1:]
            
            # Extract solver names using regex
            for solver_entry in solvers_list:
                match = re.search(r'name = "(.*?)"', solver_entry)
                if match:
                    solver_names.append(match.group(1))
    except FileNotFoundError:
        print(f"Error: Solvers configuration file not found at {file_path}.")
    except Exception as e:
        print(f"Error reading solvers file: {e}")
    
    return solver_names

def get_functions(lines: List[str]) -> List[Tuple[int, str]]:
    """
    Extracts function definitions from a list of lines in a C file.
    
    Args:
        lines (List[str]): The lines of the file.
    
    Returns:
        List[Tuple[int, str]]: A list of tuples containing line number and function name.
    """
    functions = []
    function_pattern = re.compile(
        r'^(?:static\s+)?(?:unsigned\s+|signed\s+)?(?:void|bool|int|double|float|char|long|short|struct\s+\w+|enum\s+\w+|uint|ulong)\s+(\w+)\s*\('
    )
    
    for i, line in enumerate(lines):
        match = function_pattern.match(line.strip())
        if match:
            functions.append((i + 1, match.group(1)))
    
    return functions


def remove_existing_acsl_specification(code: str) -> str:
    """
    Removes existing ACSL formal specifications from the provided C code.
    
    Args:
        code (str): The C code from which ACSL specifications should be removed.
    
    Returns:
        str: The updated code without existing ACSL specifications.
    """
    acsl_pattern = re.compile(r'/\*@(.*?)\*/', re.DOTALL)  # Matches ACSL comments
    return re.sub(acsl_pattern, '', code)

def extract_function_by_signature(code: str, function_signature: str) -> str:
    """
    Extracts the function signature and implementation of a specified function,
    removing everything else from the provided C code while correctly handling nested braces.
    
    Args:
        code (str): The C code containing multiple functions.
        function_signature (str): The function signature to extract (e.g., 'int add(int* a, int* b);').
    
    Returns:
        str: The extracted function definition with its implementation or an empty string if not found.
    """
    function_name = function_signature.split('(')[0].split()[-1]  # Extract function name
    
    # Match function signature
    signature_pattern = re.compile(rf'{re.escape(function_signature).rstrip(";")}\s*\{{', re.DOTALL)
    match = signature_pattern.search(code)
    
    if not match:
        return ""  # Function signature not found
    
    start_index = match.start()
    brace_count = 0
    in_function = False
    
    # Find the full function body by counting braces
    for i in range(start_index, len(code)):
        if code[i] == '{':
            if not in_function:
                function_start = i
                in_function = True
            brace_count += 1
        elif code[i] == '}':
            brace_count -= 1
            if brace_count == 0:
                function_end = i + 1
                return code[start_index:function_end]  # Return full function
    
    return ""  # Return empty string if function not found


def add_input_to_function(
    signature: str,
    formal_specification: str,
    natural_language_specification: str,
    header_content: str,
    interface_content: str,
    code: str
) -> str:
    """
    Finds a function with the specified name and adds additional content before it, including:
    1. Natural language specification
    2. Header file content
    3. Interface content
    4. Formal specification
    5. Function signature
    
    Args:
        signature (str): The signature of the function to modify.
        formal_specification (str): The formal specification to add above the function.
        natural_language_specification (str): The natural language description of the function.
        header_content (str): The header file content.
        interface_content (str): The interface content.
        code (str): The C code as a string.
    
    Returns:
        str: The updated code with the additional content added above the function.
    """
    code_lines = code.split("\n")
    function_definitions = get_functions(code_lines)

    signature_list = [f'{signature}']
    function_in_signature = get_functions(signature_list)
    
    for line_number, detected_function_name in function_definitions:
        if detected_function_name == function_in_signature[0][1]:
            # Insert additional content above the function definition
            insert_content = (
                f"/* Natural Language Specification \n{natural_language_specification}  */\n"
                f"/* Header File Content */\n{header_content}\n"
                f"/* Interface Content */\n{interface_content}\n"
                f"/* Formal Specification */\n{formal_specification}\n"
                f"{signature}"
            )
            code_lines.insert(line_number - 1, insert_content)
            return "\n".join(code_lines)
    
    print(f"Warning: The formal specification was not added to the code. Signature '{signature}' not found in the code.")
    return code