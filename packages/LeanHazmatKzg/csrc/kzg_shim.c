// LeanHazmatKzg: C shim wrapping ethereum/c-kzg-4844 for the Ethereum
// consensus KZG / polynomial-commitment surface (EIP-4844 blobs +
// EIP-7594 / Fulu PeerDAS cells).
//
// c-kzg is built against LeanHazmatBls's blst (the single blst owner;
// hazmat-docs/ARCHITECTURE.md §4), the lakefile compiles c-kzg's own
// `src/ckzg.c` amalgamation and links the propagated `libleanhazmat_bls`
// archive for the `blst_*` symbols.
//
// Trusted setup: embedded into the archive via `.incbin`
// (`trusted_setup_incbin.S`) and loaded once at library-load time by the
// constructor below (with a lazy fallback). No runtime file lookup; the
// `KZGSettings` is a process-lifetime, read-only singleton shared by all
// calls.
//
// Conventions (matching the other LeanHazmat families):
//   * byte inputs are `@&`-borrowed (`b_lean_obj_arg`); never mutated.
//   * byte/point results are fresh `ByteArray`s; an *empty* `ByteArray`
//     is the error sentinel (bad input length, internal failure, or the
//     setup failing to load). Multi-output operations return a Lean
//     product / arrays, empty on error.
//   * verification results are `uint8_t` (Lean `Bool`); a `false`
//     distinguishes "does not verify / bad input" from a panic, c-kzg's
//     `C_KZG_RET != C_KZG_OK` collapses to `false` here.
//
// Trust assumption (ARCHITECTURE.md §10): c-kzg-4844 + blst correctly
// implement EIP-4844 / EIP-7594. No pure-Lean reference; validated only
// against the spec KAT (LeanHazmatKzgTests).

#define _GNU_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include <lean/lean.h>
#include "ckzg.h"

// ─────────────────────────────────────────────────────────────────────
// Trusted setup: embedded bytes + load-once
// ─────────────────────────────────────────────────────────────────────

extern const char lean_hazmat_kzg_ts_start[];
extern const char lean_hazmat_kzg_ts_end[];

static KZGSettings g_settings;
static int g_attempted = 0;
static int g_load_ok   = 0;

// Load the embedded trusted setup into `g_settings` exactly once.
// `precompute = 0`: no fixed-base MSM tables, the consensus verifier
// surface (commit / prove / verify, including the Fulu cell paths) does
// not need them, and they cost ~96 MiB. Idempotent via `g_attempted`.
static void lean_hazmat_kzg_load(void) {
    if (g_attempted) return;
    g_attempted = 1;
    size_t n = (size_t)(lean_hazmat_kzg_ts_end - lean_hazmat_kzg_ts_start);
    FILE *f = fmemopen((void *)lean_hazmat_kzg_ts_start, n, "r");
    if (!f) return;
    C_KZG_RET r = load_trusted_setup_file(&g_settings, f, /*precompute=*/0);
    fclose(f);
    g_load_ok = (r == C_KZG_OK);
}

// Run at library load (dlopen for `native_decide`, or process start for a
// `lake exe`). The per-call `lean_hazmat_kzg_load()` is the lazy fallback
// for any context where the constructor doesn't fire first.
__attribute__((constructor))
static void lean_hazmat_kzg_ctor(void) { lean_hazmat_kzg_load(); }

static const KZGSettings *settings(void) {
    lean_hazmat_kzg_load();
    return g_load_ok ? &g_settings : NULL;
}

// ─────────────────────────────────────────────────────────────────────
// Byte helpers
// ─────────────────────────────────────────────────────────────────────

static inline lean_obj_res mk_bytearray(const void *src, size_t n) {
    lean_object *a = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(a), src, n);
    return a;
}
static inline lean_obj_res mk_error(void) { return lean_alloc_sarray(1, 0, 0); }

// A Lean `Prod a b` is a single 2-field constructor.
static inline lean_obj_res mk_pair(lean_obj_arg a, lean_obj_arg b) {
    lean_object *p = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p, 0, a);
    lean_ctor_set(p, 1, b);
    return p;
}

// An empty `Array ByteArray`.
static inline lean_obj_res mk_empty_arr(void) { return lean_alloc_array(0, 0); }

// Build an `Array ByteArray` of `count` items, item `i` = `base + i*sz`.
static lean_obj_res mk_bytearray_array(const uint8_t *base, size_t count, size_t sz) {
    lean_object *arr = lean_alloc_array(count, count);
    for (size_t i = 0; i < count; i++)
        lean_array_set_core(arr, i, mk_bytearray(base + i * sz, sz));
    return arr;
}

// ─────────────────────────────────────────────────────────────────────
// EIP-4844
// ─────────────────────────────────────────────────────────────────────

// blob_to_kzg_commitment : ByteArray(blob,131072) → ByteArray(commitment,48)
//   @[extern "lean_hazmat_kzg_blob_to_commitment"]
LEAN_EXPORT lean_obj_res lean_hazmat_kzg_blob_to_commitment(b_lean_obj_arg blob_a) {
    const KZGSettings *s = settings();
    if (!s) return mk_error();
    if (lean_sarray_size(blob_a) != BYTES_PER_BLOB) return mk_error();
    KZGCommitment c;
    if (blob_to_kzg_commitment(&c, (const Blob *)lean_sarray_cptr(blob_a), s) != C_KZG_OK)
        return mk_error();
    return mk_bytearray(c.bytes, BYTES_PER_COMMITMENT);
}

// compute_kzg_proof : ByteArray(blob) → ByteArray(z,32) → (proof48 × y32)
//   @[extern "lean_hazmat_kzg_compute_proof"]
// Returns a `ByteArray × ByteArray` pair; (empty, empty) on error.
LEAN_EXPORT lean_obj_res lean_hazmat_kzg_compute_proof(
    b_lean_obj_arg blob_a, b_lean_obj_arg z_a)
{
    const KZGSettings *s = settings();
    if (s && lean_sarray_size(blob_a) == BYTES_PER_BLOB
          && lean_sarray_size(z_a) == BYTES_PER_FIELD_ELEMENT) {
        KZGProof proof; Bytes32 y;
        if (compute_kzg_proof(&proof, &y,
                (const Blob *)lean_sarray_cptr(blob_a),
                (const Bytes32 *)lean_sarray_cptr(z_a), s) == C_KZG_OK)
            return mk_pair(mk_bytearray(proof.bytes, BYTES_PER_PROOF),
                           mk_bytearray(y.bytes, BYTES_PER_FIELD_ELEMENT));
    }
    return mk_pair(mk_error(), mk_error());
}

// compute_blob_kzg_proof : ByteArray(blob) → ByteArray(commitment,48) → ByteArray(proof,48)
//   @[extern "lean_hazmat_kzg_compute_blob_proof"]
LEAN_EXPORT lean_obj_res lean_hazmat_kzg_compute_blob_proof(
    b_lean_obj_arg blob_a, b_lean_obj_arg commitment_a)
{
    const KZGSettings *s = settings();
    if (!s) return mk_error();
    if (lean_sarray_size(blob_a) != BYTES_PER_BLOB) return mk_error();
    if (lean_sarray_size(commitment_a) != BYTES_PER_COMMITMENT) return mk_error();
    KZGProof proof;
    if (compute_blob_kzg_proof(&proof,
            (const Blob *)lean_sarray_cptr(blob_a),
            (const Bytes48 *)lean_sarray_cptr(commitment_a), s) != C_KZG_OK)
        return mk_error();
    return mk_bytearray(proof.bytes, BYTES_PER_PROOF);
}

// verify_kzg_proof : commitment(48) → z(32) → y(32) → proof(48) → Bool
//   @[extern "lean_hazmat_kzg_verify_proof"]
LEAN_EXPORT uint8_t lean_hazmat_kzg_verify_proof(
    b_lean_obj_arg commitment_a, b_lean_obj_arg z_a,
    b_lean_obj_arg y_a, b_lean_obj_arg proof_a)
{
    const KZGSettings *s = settings();
    if (!s) return 0;
    if (lean_sarray_size(commitment_a) != BYTES_PER_COMMITMENT) return 0;
    if (lean_sarray_size(z_a) != BYTES_PER_FIELD_ELEMENT) return 0;
    if (lean_sarray_size(y_a) != BYTES_PER_FIELD_ELEMENT) return 0;
    if (lean_sarray_size(proof_a) != BYTES_PER_PROOF) return 0;
    bool ok = false;
    if (verify_kzg_proof(&ok,
            (const Bytes48 *)lean_sarray_cptr(commitment_a),
            (const Bytes32 *)lean_sarray_cptr(z_a),
            (const Bytes32 *)lean_sarray_cptr(y_a),
            (const Bytes48 *)lean_sarray_cptr(proof_a), s) != C_KZG_OK)
        return 0;
    return ok ? 1 : 0;
}

// verify_blob_kzg_proof : blob → commitment(48) → proof(48) → Bool
//   @[extern "lean_hazmat_kzg_verify_blob_proof"]
LEAN_EXPORT uint8_t lean_hazmat_kzg_verify_blob_proof(
    b_lean_obj_arg blob_a, b_lean_obj_arg commitment_a, b_lean_obj_arg proof_a)
{
    const KZGSettings *s = settings();
    if (!s) return 0;
    if (lean_sarray_size(blob_a) != BYTES_PER_BLOB) return 0;
    if (lean_sarray_size(commitment_a) != BYTES_PER_COMMITMENT) return 0;
    if (lean_sarray_size(proof_a) != BYTES_PER_PROOF) return 0;
    bool ok = false;
    if (verify_blob_kzg_proof(&ok,
            (const Blob *)lean_sarray_cptr(blob_a),
            (const Bytes48 *)lean_sarray_cptr(commitment_a),
            (const Bytes48 *)lean_sarray_cptr(proof_a), s) != C_KZG_OK)
        return 0;
    return ok ? 1 : 0;
}

// Copy `n` parallel `ByteArray`s of fixed size `sz` into a fresh packed
// C buffer. Returns NULL on any length mismatch (caller treats as error).
static uint8_t *pack_fixed(b_lean_obj_arg arr, size_t n, size_t sz) {
    if (lean_array_size(arr) != n) return NULL;
    uint8_t *buf = (uint8_t *)malloc(n * sz);
    if (!buf && n) return NULL;
    for (size_t i = 0; i < n; i++) {
        lean_object *e = lean_array_get_core(arr, i);
        if (lean_sarray_size(e) != sz) { free(buf); return NULL; }
        memcpy(buf + i * sz, lean_sarray_cptr(e), sz);
    }
    return buf;
}

// verify_blob_kzg_proof_batch : Array blob → Array commitment → Array proof → Bool
//   @[extern "lean_hazmat_kzg_verify_blob_proof_batch"]
LEAN_EXPORT uint8_t lean_hazmat_kzg_verify_blob_proof_batch(
    b_lean_obj_arg blobs_a, b_lean_obj_arg commitments_a, b_lean_obj_arg proofs_a)
{
    const KZGSettings *s = settings();
    if (!s) return 0;
    size_t n = lean_array_size(blobs_a);
    if (lean_array_size(commitments_a) != n) return 0;
    if (lean_array_size(proofs_a) != n) return 0;

    uint8_t result = 0;
    uint8_t *blobs = pack_fixed(blobs_a, n, BYTES_PER_BLOB);
    uint8_t *coms  = pack_fixed(commitments_a, n, BYTES_PER_COMMITMENT);
    uint8_t *prfs  = pack_fixed(proofs_a, n, BYTES_PER_PROOF);
    if (blobs && coms && prfs) {
        bool ok = false;
        if (verify_blob_kzg_proof_batch(&ok,
                (const Blob *)blobs, (const Bytes48 *)coms,
                (const Bytes48 *)prfs, (uint64_t)n, s) == C_KZG_OK)
            result = ok ? 1 : 0;
    }
    free(blobs); free(coms); free(prfs);
    return result;
}

// ─────────────────────────────────────────────────────────────────────
// EIP-7594 / Fulu PeerDAS cells
// ─────────────────────────────────────────────────────────────────────

// compute_cells_and_kzg_proofs : blob → (Array cell × Array proof)
//   @[extern "lean_hazmat_kzg_compute_cells_and_proofs"]
// Returns (cells[128]×2048, proofs[128]×48); (#[], #[]) on error.
LEAN_EXPORT lean_obj_res lean_hazmat_kzg_compute_cells_and_proofs(
    b_lean_obj_arg blob_a)
{
    const KZGSettings *s = settings();
    if (s && lean_sarray_size(blob_a) == BYTES_PER_BLOB) {
        Cell *cells = (Cell *)malloc(sizeof(Cell) * CELLS_PER_EXT_BLOB);
        KZGProof *proofs = (KZGProof *)malloc(sizeof(KZGProof) * CELLS_PER_EXT_BLOB);
        if (cells && proofs &&
            compute_cells_and_kzg_proofs(cells, proofs,
                (const Blob *)lean_sarray_cptr(blob_a), s) == C_KZG_OK) {
            lean_object *cellArr =
                mk_bytearray_array((const uint8_t *)cells, CELLS_PER_EXT_BLOB, BYTES_PER_CELL);
            lean_object *proofArr =
                mk_bytearray_array((const uint8_t *)proofs, CELLS_PER_EXT_BLOB, BYTES_PER_PROOF);
            free(cells); free(proofs);
            return mk_pair(cellArr, proofArr);
        }
        free(cells); free(proofs);
    }
    return mk_pair(mk_empty_arr(), mk_empty_arr());
}

// Read an `Array UInt64` into a fresh C `uint64_t[]`. NULL on alloc fail.
static uint64_t *pack_u64(b_lean_obj_arg arr, size_t n) {
    uint64_t *buf = (uint64_t *)malloc(n * sizeof(uint64_t));
    if (!buf && n) return NULL;
    for (size_t i = 0; i < n; i++)
        buf[i] = lean_unbox_uint64(lean_array_get_core(arr, i));
    return buf;
}

// verify_cell_kzg_proof_batch :
//   Array commitment(48) → Array UInt64(cellIndices) → Array cell(2048)
//     → Array proof(48) → Bool
//   @[extern "lean_hazmat_kzg_verify_cell_proof_batch"]
// All four arrays must share the same length `num_cells`.
LEAN_EXPORT uint8_t lean_hazmat_kzg_verify_cell_proof_batch(
    b_lean_obj_arg commitments_a, b_lean_obj_arg indices_a,
    b_lean_obj_arg cells_a, b_lean_obj_arg proofs_a)
{
    const KZGSettings *s = settings();
    if (!s) return 0;
    size_t n = lean_array_size(cells_a);
    if (lean_array_size(commitments_a) != n) return 0;
    if (lean_array_size(indices_a) != n) return 0;
    if (lean_array_size(proofs_a) != n) return 0;

    uint8_t result = 0;
    uint8_t  *coms  = pack_fixed(commitments_a, n, BYTES_PER_COMMITMENT);
    uint8_t  *cells = pack_fixed(cells_a, n, BYTES_PER_CELL);
    uint8_t  *prfs  = pack_fixed(proofs_a, n, BYTES_PER_PROOF);
    uint64_t *idx   = pack_u64(indices_a, n);
    if (coms && cells && prfs && idx) {
        bool ok = false;
        if (verify_cell_kzg_proof_batch(&ok,
                (const Bytes48 *)coms, idx, (const Cell *)cells,
                (const Bytes48 *)prfs, (uint64_t)n, s) == C_KZG_OK)
            result = ok ? 1 : 0;
    }
    free(coms); free(cells); free(prfs); free(idx);
    return result;
}

// recover_cells_and_kzg_proofs :
//   Array UInt64(cellIndices) → Array cell(2048)
//     → (Array cell[128] × Array proof[128])
//   @[extern "lean_hazmat_kzg_recover_cells_and_proofs"]
// `cellIndices` and `cells` are the (≥50%) known subset. Returns the full
// recovered 128 cells + 128 proofs; (#[], #[]) on error.
LEAN_EXPORT lean_obj_res lean_hazmat_kzg_recover_cells_and_proofs(
    b_lean_obj_arg indices_a, b_lean_obj_arg cells_a)
{
    const KZGSettings *s = settings();
    size_t n = lean_array_size(cells_a);
    if (s && lean_array_size(indices_a) == n) {
        uint8_t  *cells = pack_fixed(cells_a, n, BYTES_PER_CELL);
        uint64_t *idx   = pack_u64(indices_a, n);
        Cell *rc = (Cell *)malloc(sizeof(Cell) * CELLS_PER_EXT_BLOB);
        KZGProof *rp = (KZGProof *)malloc(sizeof(KZGProof) * CELLS_PER_EXT_BLOB);
        if (cells && idx && rc && rp &&
            recover_cells_and_kzg_proofs(rc, rp, idx, (const Cell *)cells,
                (uint64_t)n, s) == C_KZG_OK) {
            lean_object *cellArr =
                mk_bytearray_array((const uint8_t *)rc, CELLS_PER_EXT_BLOB, BYTES_PER_CELL);
            lean_object *proofArr =
                mk_bytearray_array((const uint8_t *)rp, CELLS_PER_EXT_BLOB, BYTES_PER_PROOF);
            free(cells); free(idx); free(rc); free(rp);
            return mk_pair(cellArr, proofArr);
        }
        free(cells); free(idx); free(rc); free(rp);
    }
    return mk_pair(mk_empty_arr(), mk_empty_arr());
}
