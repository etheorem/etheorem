# LeanHazmatXMSS

Lean 4 FFI bindings for RFC 8391 XMSS, wrapping [xmss-reference](https://github.com/XMSS/xmss-reference). Part of the
[LeanHazmat](../../hazmat-docs/ARCHITECTURE.md) FFI crypto family

## Setup


```bash
lake build LeanHazmatXMSS
```

To depend on it from another package:

```toml
[[require]]
name = "LeanHazmatXMSS"
path = "…/packages/LeanHazmatXMSS"     # or a git source
```

## Usage



### Running and checking


## API (namespace `LeanHazmat.XMSS`)


## Trust boundary

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md).

## Tests

```bash
lake build LeanHazmatXMSSTests     
```

## License

LGPL-3.0-only, see the umbrella [`LICENSE`](../../LICENSE).
