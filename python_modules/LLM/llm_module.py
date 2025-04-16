import llm
import os
from typing import Dict, List
from python_modules.helper_files.filesystem_io import read_file

SUPPORTED_LLMs = ["o1", "o3-mini", "gpt-4o-latest", "gpt-4o-mini"]

def load_prompt_templates() -> Dict[str, str]:
    """
    Loads prompt templates from the file system.
    
    Returns:
        Dict[str, str]: A dictionary containing the loaded templates.
    """
    return {
        "initial_prompt": read_file("./prompts/initial_prompt_template.txt"),
        "repair_prompt": read_file("./prompts/repair_prompt_template.txt"),
    }

def initialize_llms() -> Dict[str, object]:
    """
    Initializes available LLM models.
    
    Returns:
        Dict[str, object]: A dictionary containing initialized LLM models.
    """
    llm_o3_mini, llm_o1 = build_o1_series()
    llm_gpt_4o_latest, llm_gpt_4o_mini = build_openai_latest_and_fastest()
    
    models = {
        "o1": llm_o1,
        "o3-mini": llm_o3_mini,
        "gpt-4o-latest": llm_gpt_4o_latest,
        "gpt-4o-mini": llm_gpt_4o_mini,
    }

    return models

def prompt(model: llm.Model, prompt: str):
    res = model.prompt(prompt, stream=False)
    return res

def prompt_with_temp(model: llm.Model, prompt: str, temperature: float = 0.7):
    """
    Send a prompt to the model with a specified temperature.

    Args:
    model (llm.Model): The LLM model to use.
    prompt (str): The prompt to send to the model.
    temperature (float): The temperature setting for the model's response. Default is 0.7.

    Returns:
    str: The model's response text.
    """
    model_id = model.model_id
    if "o1" in model_id or "gemini" in model_id:
        temperature = 1
        return model.prompt(prompt, stream=False)

    return model.prompt(prompt, stream=False, temperature=temperature)

def get_model_name(model: llm.Model):
    return model.model_id

# Function to add the previous attempt to the prompt along with some information about it
def add_previous_attempt_feedback(previous_attempt: str, natural_language_included: bool = False, formal_specification_included: bool = False, previous_attempt_feedback: str = ""):
    # If no previous attempt is given, return an empty string
    if previous_attempt == "":
        return ""

    # If only natural language is included then give a message that the previous attempt did not verify, but no formal specification was given
    if natural_language_included and not formal_specification_included:
        return "The previous code attempt did not verify: \n" + previous_attempt + "Improve the code such that it formally verifies."

    # If a formal specification is included, then give a message that the previous attempt did not verify
    if formal_specification_included:
        return "The previous code attempt did not verify: \n```C" + previous_attempt + "``` The following feedback was given: \n" + previous_attempt_feedback + "\nPlease improve the code such that it formally verifies."

def build_openai_latest_and_fastest():
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")

    gpt_4o_latest: llm.Model = llm.get_model("gpt-4o")
    gpt_4o_latest.key = OPENAI_API_KEY

    gpt_4o_mini_model: llm.Model = llm.get_model("gpt-4o-mini")
    gpt_4o_mini_model.key = OPENAI_API_KEY

    return gpt_4o_latest, gpt_4o_mini_model


def build_o1_series():
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
    o3_mini_model: llm.Model = llm.get_model("o3-mini")
    o3_mini_model.key = OPENAI_API_KEY

    o1_model: llm.Model = llm.get_model("o1")
    o1_model.key = OPENAI_API_KEY
    
    return o3_mini_model, o1_model


def format_prompt(template_type: str, C_code_input: str, previous_attempt: str = "") -> str:
    """
    Returns:
        str: The formatted prompt.
        C_code_input: The C code input to be used in the prompt
        previous_attempt: The previous attempt to be used in the prompt
    """
    templates = load_prompt_templates()
    selected_template = templates.get(template_type)
    if not selected_template:
        raise ValueError("Invalid template type specified.")    
    
    return selected_template.replace(f"{{{{{'C_CODE'}}}}}", C_code_input).replace(f"{{{{{'PREVIOUS_ATTEMPT'}}}}}", previous_attempt)

def ensure_supported_llms(llms: List[str]) -> None:
    """
    Ensures that the specified LLMs are supported.
    
    Args:
        llms (List[str]): A list of LLM identifiers.
    
    Raises:
        ValueError: If an unsupported LLM is specified.
    """
    for llm in llms:
        if llm not in SUPPORTED_LLMs:
            raise ValueError(f"Error: {llm} is not a supported LLM. Supported LLMs are: {SUPPORTED_LLMs}.")