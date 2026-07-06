// LeanHazmatKzg — embed the KZG trusted setup into the archive.
//
// `.incbin` copies the file's *contents* into the `.rodata` section at
// assemble time, so the trusted setup travels inside the
// `libleanhazmat_kzg` archive with no runtime file lookup — the package
// is self-contained and hermetic. The path is supplied at build time by
// the lakefile via `-D TRUSTED_SETUP_PATH="\"<abs>/data/trusted_setup.txt\""`
// (the `.S` extension means `cc` runs the C preprocessor first, so the
// macro expands before the assembler sees `.incbin`). Only the build-time
// path matters; the emitted object holds the bytes, not the path.
//
// The setup is the fixed EIP-4844 KZG ceremony output shipped with c-kzg
// (`data/trusted_setup.txt`, refreshed from the pinned tag by
// `just hazmat-kzg-vendor`). The C shim reads these bytes via `fmemopen` +
// `load_trusted_setup_file` once at library load.

    #ifdef __APPLE__
    .section __DATA,__const
    #else
    .section .rodata
    #endif

    .global lean_hazmat_kzg_ts_start
lean_hazmat_kzg_ts_start:
    .incbin TRUSTED_SETUP_PATH
    .global lean_hazmat_kzg_ts_end
lean_hazmat_kzg_ts_end:
