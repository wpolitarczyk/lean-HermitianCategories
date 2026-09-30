FROM mcr.microsoft.com/devcontainers/base:ubuntu

# Install basic dependencies needed for Lean and the Mathlib cache
RUN apt-get update && apt-get install -y curl git wget build-essential

USER vscode

# Install elan (Lean toolchain manager) for the vscode user
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add elan to the PATH
ENV PATH="/home/vscode/.elan/bin:${PATH}"
