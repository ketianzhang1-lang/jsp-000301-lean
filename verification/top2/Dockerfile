FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git python3 build-essential pkg-config zstd && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan CARGO_HOME=/opt/cargo RUSTUP_HOME=/opt/rustup
ENV PATH=/opt/elan/bin:/opt/cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN curl -sSf https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh && sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path && elan toolchain install leanprover/lean4:v4.34.0
RUN curl -sSf https://sh.rustup.rs -o /tmp/rust-init.sh && sh /tmp/rust-init.sh -y --profile minimal --no-modify-path
RUN useradd --create-home --uid 10001 verifier && chmod -R a+rX /opt/elan /opt/cargo /opt/rustup
USER verifier
WORKDIR /work
