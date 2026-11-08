# The `tauto` command only. Mount a project at /work to use it:
#   docker build -t tauto .
#   docker run --rm -v "$PWD:/work" tauto check meta/KernelSafe.taut

FROM rust:1-slim-bookworm@sha256:86234e857a413004348b471d11a4ebe1aa92d2eae2b6b143cac68fd1ac3c48be AS build
# git: the workspace has git dependencies.
RUN apt-get update \
 && apt-get install -y --no-install-recommends git ca-certificates \
 && rm -rf /var/lib/apt/lists/*
WORKDIR /src
COPY . .
# rustup installs the nightly pinned in rust-toolchain.toml on first use.
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/usr/local/cargo/git \
    --mount=type=cache,target=/src/target \
    cargo build --locked --release -p tauto-cli --bin tauto \
 && install -D target/release/tauto /out/tauto

FROM debian:bookworm-slim@sha256:7ff6ba31527b9e336162fa061746c366c4b2032f4d2cff2078bea43f78efe3f8
COPY --from=build /out/tauto /usr/local/bin/tauto
WORKDIR /work
ENTRYPOINT ["tauto"]
