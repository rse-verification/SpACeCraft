import subprocess, os

def compile_c(source_path, build_dir):
    os.makedirs(build_dir, exist_ok=True)
    base = os.path.splitext(os.path.basename(source_path))[0]
    out = os.path.join(build_dir, base)

    # If you want an executable, omit "-c"; if you just want to compile to .o, keep it.
    cmd = ["gcc", source_path, "-o", out]  # no "-c"
    proc = subprocess.run(cmd, capture_output=True, text=True)

    # Optionally remove the file if you only care about success, not the artifact:
    if os.path.exists(out):
        os.remove(out)

    success = (proc.returncode == 0)
    return success, proc.stdout + proc.stderr
