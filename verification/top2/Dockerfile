FROM rust:1.90.0-slim-bookworm
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git python3 build-essential pkg-config zstd && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/toolchains/leanprover--lean4---v4.34.0/bin:/opt/elan/bin:/usr/local/cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN curl -sSf https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh && sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path && elan toolchain install leanprover/lean4:v4.34.0
RUN useradd --create-home --uid 10001 verifier && chmod -R a+rX /opt/elan
USER verifier
WORKDIR /work
