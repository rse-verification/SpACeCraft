import os
from typing import Dict, List
from python_modules.helper_files.filesystem_io import read_file
import llm

# Define valid case studies
SUPPORTED_LLMs = ["o1", "o3-mini", "gpt-4o-latest", "gpt-4o-mini"]



def build_openai_latest_and_fastest():
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")

    gpt_4o_latest: llm.Model = llm.get_model("gpt-4o")
    gpt_4o_latest.key = OPENAI_API_KEY

    gpt_4o_mini_model: llm.Model = llm.get_model("gpt-4o-mini")
    gpt_4o_mini_model.key = OPENAI_API_KEY

    gpt_45_preview: llm.Model = llm.get_model("gpt-4.5-preview")
    gpt_4o_mini_model.key = OPENAI_API_KEY

    return gpt_4o_latest, gpt_4o_mini_model, gpt_45_preview


def build_o1_series():
    OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")

    o1_mini_model: llm.Model = llm.get_model("o1-mini")
    o1_mini_model.key = OPENAI_API_KEY

    o1_preview_model: llm.Model = llm.get_model("o1-preview")
    o1_preview_model.key = OPENAI_API_KEY
    
    o3_mini_model: llm.Model = llm.get_model("o3-mini")
    o3_mini_model.key = OPENAI_API_KEY

    o1_model: llm.Model = llm.get_model("o1")
    o1_model.key = OPENAI_API_KEY
    
    return o1_mini_model, o1_preview_model, o3_mini_model, o1_model


def load_prompt_templates() -> Dict[str, str]:
    """
    Loads prompt templates from the file system.
    
    Returns:
        Dict[str, str]: A dictionary containing the loaded templates.
    """
    return {
        "initial_prompt": read_file("./initial_prompt_template.txt"),
        "repair_prompt": read_file("./repair_prompt_template.txt"),
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

def format_prompt(template_type: str, C_code_input: str) -> str:
    """
    Formats a prompt by replacing placeholders with case study inputs.

    Returns:
        str: The formatted prompt.
        C_code_input: The C code input to be used in the prompt
    """
    templates = load_prompt_templates()
    selected_template = templates.get(template_type)
    if not selected_template:
        raise ValueError("Invalid template type specified.")    
    
    return selected_template.replace(f"{{{{{"C_CODE"}}}}}", C_code_input)

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