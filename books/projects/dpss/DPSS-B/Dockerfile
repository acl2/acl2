FROM jupyter/minimal-notebook:latest

USER root
RUN apt-get update && \
    apt-get install --no-install-recommends -y \
    python3 \
    python3-pip \
    python-is-python3 \
    python3-tk

RUN pip install z3-solver

USER jovyan
