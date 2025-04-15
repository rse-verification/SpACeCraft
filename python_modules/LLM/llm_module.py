import llm
from mako.template import Template

def conditional_render(prompt, context, start_delim="% if", end_delim="% endif"):
    template = Template(prompt)
    return template.render(**context)


def parse_markdown_backticks(str, gemini_output = False) -> str:
    if "```" not in str:
        return str.strip()
    
    # Remove opening backticks and language identifier
    str = str.split("```", 1)[-1].split("\n", 1)[-1]

    # Remove closing backticks
    str = str.rsplit("```", 1)[0]
    # Remove any leading or trailing whitespace
    return str.strip()

def prompt(model: llm.Model, prompt: str):
    res = model.prompt(prompt, stream=False)
    return res.text()


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
        res = model.prompt(prompt, stream=False)
        return res.text()

    res = model.prompt(prompt, stream=False, temperature=temperature)
    return res.text()

def get_model_name(model: llm.Model):
    return model.model_id


