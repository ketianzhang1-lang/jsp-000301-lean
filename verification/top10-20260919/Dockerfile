FROM ubuntu:24.04
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends python3 git curl ca-certificates zstd build-essential pkg-config && rm -rf /var/lib/apt/lists/*
RUN useradd --create-home --uid 2000 verifier
USER verifier
WORKDIR /work
