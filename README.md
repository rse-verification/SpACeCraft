# SpecSmith

A fork of VeCoGen that generates ACSL specifications from C code using an LLM and the Why3/Frama-C toolchain.

---

## 📂 Branches

This repo maintains two ways of running the tool:

- **`local`** – for running SpecSmith directly on your host, with Python, Frama-C, Why3, etc.
- **`docker`** – for running SpecSmith entirely inside a Docker container (no local toolchain installs).

## Local Workflow

Prerequisites

- Python ≥ 3.6 + virtual environments
- Frama-C (https://frama-c.com/)
- Why3 (https://why3.lri.fr/) + provers: Alt-Ergo, CVC4, Z3

# 1. Clone & switch

git clone <repo-url>
cd SpecSmith

# 2. Create & activate a virtualenv

python3 -m venv .venv
. .venv/bin/activate

# 3. Install dependencies

pip install -r requirements.txt

# 4. Set your API key

echo "OPENAI*API_KEY=sk*..." > .env

# 5. Run SpecSmith

python main.py --directory ./input

## 🐳 Docker Workflow

Prerequisites

- Docker (Engine & CLI)
- LLM API key

# 1. Pull the container image

docker pull ghcr.io/sevenhuijsenm/specsmith:latest

# 2. Run interactively, mounting host folders:

docker run --rm -it \
 --mount type=bind,source="$(pwd)/input",target=/app/input \
  --mount type=bind,source="$(pwd)/output",target=/app/output \
 -e OPENAI_API_KEY \
 ghcr.io/sevenhuijsenm/specsmith:latest

# 3. Inside the container, use:

python main.py --directory ./input

## CLI Parameters

Flag Description Default
-d, --directory Input folder containing .c files ./input (or /app/input)
-o, --output_path Destination for generated ACSL specs ./output (or /app/output)
-tmp, --temp_folder Folder for temporary files ../tmp (or /app/tmp)
-model, --model_name LLM model to use o4-mini
-iter, --iterations Number of LLM iterations per file 1
-temp, --temperature Sampling temperature for the LLM 1.0
-ieg, --initial_examples_generated Initial example specs to generate per file 3

🚀 Next Steps
Drop your .c files into the input/ folder on the chosen branch.

Ensure OPENAI_API_KEY is set (host env or .env).

Run the tool locally or in Docker.

Inspect generated ACSL specs in output/.
