
import subprocess

def run_command(command: str, timeout: int) -> tuple:
    """
    Runs a shell command with a specified timeout.
    
    Args:
        command (str): The command to execute.
        timeout (int): The maximum time in seconds the command can run.

    Returns:
        tuple: (str, str, bool)
            - Standard output from the command.
            - Standard error from the command.
            - True if command completed successfully, False if it timed out.
    """
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    try:
        process.wait(timeout=timeout)
        stdout, stderr = process.communicate()
        return stdout.decode("utf-8"), stderr.decode("utf-8"), True
    except subprocess.TimeoutExpired:
        process.kill()
        return "", "Timeout", False
