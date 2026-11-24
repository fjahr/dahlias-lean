/* Differential test driver for libsecp256k1's fullagg module.
 *
 * Reads the cases of scripts/fuzz.py from standard input (see scripts/Fuzz.lean
 * for the format) and prints one result per line.
 *
 * The C API takes parsed objects of fixed size. A field of the wrong length
 * cannot be passed at all; those cases print SKIP. A public key, public nonce,
 * aggregate nonce or partial signature that the library's parse function
 * rejects counts as a failure of the algorithm, as it does in the reference
 * runner.
 *
 * Sign: the BIP finds the signer's index, the C API takes it as an argument.
 * The driver tries every index and reports the first success. The secret
 * nonce object is filled in directly from the 64 bytes of the case, with the
 * layout of secp256k1_fullagg_secnonce_save (magic, r1, r2, public key).
 *
 * NonceGen: secp256k1_fullagg_nonce_gen takes extra_input32 as 32 bytes or
 * NULL, so other lengths print SKIP. Lines of kind `C` call
 * secp256k1_fullagg_nonce_gen_counter with the counter and the key pair of the
 * secret key.
 *
 * Two kinds of cases test the state the C API keeps and have no counterpart in
 * the BIP's algorithms:
 * - `R`, with the fields of `S`: sign, then sign with a secnonce object made
 *   for another public key, then sign again with the first secnonce object.
 *   Prints the partial signature, a note if the other key was accepted, and
 *   whether the last call was rejected.
 * - `X`, with the fields of `S` and a second set of lists: initialize the
 *   session with the first lists and sign with the second. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <secp256k1.h>
#include <secp256k1_extrakeys.h>
#include <secp256k1_fullagg.h>

#define MAXN 16
#define MAXF 256

static const unsigned char secnonce_magic[4] = { 0xf1, 0x1a, 0x99, 0x01 };

static int illegal = 0;
static void on_illegal(const char *msg, void *data) { (void)msg; (void)data; illegal = 1; }

static int hexval(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

/* Decode a hex field ("_" is empty). Returns the length, or -1 if it does not fit. */
static long unhex(const char *s, unsigned char *out, size_t cap) {
    size_t i, slen = strlen(s);
    if (slen == 1 && s[0] == '_') return 0;
    if (slen % 2 || slen / 2 > cap) return -1;
    for (i = 0; i < slen / 2; i++) out[i] = (unsigned char)(hexval(s[2 * i]) * 16 + hexval(s[2 * i + 1]));
    return (long)(slen / 2);
}

typedef struct { int n; int bad_len; unsigned char v[MAXN][MAXF]; } list;

/* Parse "a,b,..." (or "-") into fields that must all have length `want`. */
static void parse_list(char *s, size_t want, list *l) {
    char *item, *save;
    l->n = 0; l->bad_len = 0;
    if (strcmp(s, "-") == 0) return;
    for (item = strtok_r(s, ",", &save); item != NULL; item = strtok_r(NULL, ",", &save)) {
        if (l->n >= MAXN) { l->bad_len = 1; return; }
        if (unhex(item, l->v[l->n], MAXF) != (long)want) l->bad_len = 1;
        l->n++;
    }
}

static void print_hex(const unsigned char *b, size_t len) {
    size_t i;
    for (i = 0; i < len; i++) printf("%02x", b[i]);
}

static const secp256k1_context *ctx;
static list pks_l, msgs_l, nonces_l, psigs_l;
static secp256k1_xonly_pubkey pks[MAXN];
static secp256k1_fullagg_pubnonce nonces[MAXN];
static secp256k1_fullagg_partial_sig psigs[MAXN];
static const secp256k1_xonly_pubkey *pk_ptrs[MAXN];
static const unsigned char *msg_ptrs[MAXN];
static const secp256k1_fullagg_pubnonce *nonce_ptrs[MAXN];
static const secp256k1_fullagg_partial_sig *psig_ptrs[MAXN];

/* Returns 1 if all objects parse, 0 if one is rejected. */
static int load_pks(void) {
    int i;
    for (i = 0; i < pks_l.n; i++) {
        if (!secp256k1_xonly_pubkey_parse(ctx, &pks[i], pks_l.v[i])) return 0;
        pk_ptrs[i] = &pks[i];
        msg_ptrs[i] = i < msgs_l.n ? msgs_l.v[i] : NULL;
    }
    return 1;
}

static int load_nonces(void) {
    int i;
    for (i = 0; i < nonces_l.n; i++) {
        if (!secp256k1_fullagg_pubnonce_parse(ctx, &nonces[i], nonces_l.v[i])) return 0;
        nonce_ptrs[i] = &nonces[i];
    }
    return 1;
}

static int load_psigs(void) {
    int i;
    for (i = 0; i < psigs_l.n; i++) {
        if (!secp256k1_fullagg_partial_sig_parse(ctx, &psigs[i], psigs_l.v[i])) return 0;
        psig_ptrs[i] = &psigs[i];
    }
    return 1;
}

static void do_noncegen(char *rand_s, char *sk_s, char *extra_s) {
    unsigned char rand[32], sk[32], one[32] = {0}, extra[MAXF], ser[66];
    secp256k1_keypair kp;
    secp256k1_xonly_pubkey pk;
    secp256k1_fullagg_secnonce sec;
    secp256k1_fullagg_pubnonce pub;
    int has_sk = strcmp(sk_s, "-") != 0;
    long elen = unhex(extra_s, extra, MAXF);
    one[31] = 1;
    if (unhex(rand_s, rand, 32) != 32 || (has_sk && unhex(sk_s, sk, 32) != 32) || (elen != 0 && elen != 32)) {
        printf("SKIP\n"); return;
    }
    /* The public key only ends up in the secnonce object; it is not hashed.
     * An invalid sk has no public key, and nonce_gen must reject it with any. */
    if (!secp256k1_keypair_create(ctx, &kp, has_sk ? sk : one) && !secp256k1_keypair_create(ctx, &kp, one)) {
        printf("FAIL\n"); return;
    }
    if (!secp256k1_keypair_xonly_pub(ctx, &pk, NULL, &kp)) {
        printf("FAIL\n"); return;
    }
    if (!secp256k1_fullagg_nonce_gen(ctx, &sec, &pub, rand, has_sk ? sk : NULL, &pk, elen ? extra : NULL)) {
        printf("FAIL\n"); return;
    }
    secp256k1_fullagg_pubnonce_serialize(ctx, ser, &pub);
    print_hex(&sec.data[4], 64); printf(":"); print_hex(ser, 66); printf("\n");
}

static void do_noncegen_counter(char *cnt_s, char *sk_s, char *extra_s) {
    unsigned char cnt[8], sk[32], extra[MAXF], ser[66];
    secp256k1_keypair kp;
    secp256k1_fullagg_secnonce sec;
    secp256k1_fullagg_pubnonce pub;
    uint64_t c = 0;
    int i;
    long elen = unhex(extra_s, extra, MAXF);
    if (unhex(cnt_s, cnt, 8) != 8 || unhex(sk_s, sk, 32) != 32 || (elen != 0 && elen != 32)) {
        printf("SKIP\n"); return;
    }
    for (i = 0; i < 8; i++) c = (c << 8) | cnt[i];
    if (!secp256k1_keypair_create(ctx, &kp, sk)) {
        printf("FAIL\n"); return;
    }
    if (!secp256k1_fullagg_nonce_gen_counter(ctx, &sec, &pub, c, &kp, elen ? extra : NULL)) {
        printf("FAIL\n"); return;
    }
    secp256k1_fullagg_pubnonce_serialize(ctx, ser, &pub);
    print_hex(&sec.data[4], 64); printf(":"); print_hex(ser, 66); printf("\n");
}

static void do_nonceagg(char *nonces_s) {
    secp256k1_fullagg_aggnonce agg;
    unsigned char ser[66];
    parse_list(nonces_s, 66, &nonces_l);
    if (nonces_l.bad_len) { printf("SKIP\n"); return; }
    if (!load_nonces() || !secp256k1_fullagg_nonce_agg(ctx, &agg, nonce_ptrs, (size_t)nonces_l.n)) {
        printf("FAIL\n"); return;
    }
    secp256k1_fullagg_aggnonce_serialize(ctx, ser, &agg);
    print_hex(ser, 66); printf("\n");
}

/* Parse the lists and the aggregate nonce and initialize the session.
 * Returns 1 on success, 0 on failure, -1 if the case cannot be expressed. */
static int session(char *agg_s, char *pks_s, char *msgs_s, char *nonces_s, secp256k1_fullagg_session *sess) {
    unsigned char aggb[66];
    secp256k1_fullagg_aggnonce agg;
    long alen = unhex(agg_s, aggb, 66);
    parse_list(pks_s, 32, &pks_l);
    parse_list(msgs_s, 32, &msgs_l);
    parse_list(nonces_s, 66, &nonces_l);
    if (alen != 66 || pks_l.bad_len || msgs_l.bad_len || nonces_l.bad_len) return -1;
    if (pks_l.n != msgs_l.n || pks_l.n != nonces_l.n || pks_l.n == 0) return 0;
    if (!load_pks() || !load_nonces() || !secp256k1_fullagg_aggnonce_parse(ctx, &agg, aggb)) return 0;
    return secp256k1_fullagg_session_init(ctx, sess, &agg, pk_ptrs, msg_ptrs, nonce_ptrs, (size_t)pks_l.n);
}

/* Sign with the lists that are loaded, in the given session. With `reuse`,
 * sign a second time with the same secnonce object and report the outcome,
 * and before that sign with a secnonce object that was made for another
 * public key, which must fail. */
static void sign_loaded(const unsigned char *secb, const unsigned char *sk, const unsigned char *m,
                        const secp256k1_fullagg_session *sess, int reuse) {
    unsigned char out[32];
    secp256k1_keypair kp;
    secp256k1_pubkey pub;
    int j;
    if (!secp256k1_keypair_create(ctx, &kp, sk) || !secp256k1_keypair_pub(ctx, &pub, &kp)) {
        printf("FAIL\n"); return;
    }
    for (j = 0; j < pks_l.n; j++) {
        secp256k1_fullagg_secnonce sec;
        secp256k1_fullagg_partial_sig psig, psig2;
        memcpy(&sec.data[0], secnonce_magic, 4);
        memcpy(&sec.data[4], secb, 64);
        memcpy(&sec.data[68], pub.data, 64);
        illegal = 0;
        if (secp256k1_fullagg_partial_sign(ctx, &psig, &sec, &kp, m, sess, pk_ptrs, msg_ptrs, nonce_ptrs, (size_t)pks_l.n, (size_t)j) && !illegal) {
            secp256k1_fullagg_partial_sig_serialize(ctx, out, &psig);
            print_hex(out, 32);
            if (reuse) {
                secp256k1_fullagg_secnonce other;
                secp256k1_keypair kp2;
                secp256k1_pubkey pub2;
                unsigned char sk2[32] = {0};
                sk2[31] = 2;
                if (memcmp(sk, sk2, 32) == 0) sk2[31] = 3;
                if (secp256k1_keypair_create(ctx, &kp2, sk2) && secp256k1_keypair_pub(ctx, &pub2, &kp2)) {
                    memcpy(&other.data[0], secnonce_magic, 4);
                    memcpy(&other.data[4], secb, 64);
                    memcpy(&other.data[68], pub2.data, 64);
                    illegal = 0;
                    if (secp256k1_fullagg_partial_sign(ctx, &psig2, &other, &kp, m, sess, pk_ptrs, msg_ptrs, nonce_ptrs, (size_t)pks_l.n, (size_t)j) && !illegal) {
                        printf(":otherkey-accepted");
                    }
                }
                illegal = 0;
                if (secp256k1_fullagg_partial_sign(ctx, &psig2, &sec, &kp, m, sess, pk_ptrs, msg_ptrs, nonce_ptrs, (size_t)pks_l.n, (size_t)j) && !illegal) {
                    printf(":reuse-accepted");
                } else {
                    printf(":reuse-rejected");
                }
            }
            printf("\n");
            return;
        }
    }
    printf("FAIL\n");
}

static void do_sign(char *sec_s, char *sk_s, char *m_s, char *agg_s, char *pks_s, char *msgs_s, char *nonces_s, int reuse) {
    unsigned char secb[64], sk[32], m[32];
    secp256k1_fullagg_session sess;
    int r;
    if (unhex(sec_s, secb, 64) != 64 || unhex(sk_s, sk, 32) != 32 || unhex(m_s, m, 32) != 32) {
        printf("SKIP\n"); return;
    }
    r = session(agg_s, pks_s, msgs_s, nonces_s, &sess);
    if (r < 0) { printf("SKIP\n"); return; }
    if (r == 0) { printf("FAIL\n"); return; }
    sign_loaded(secb, sk, m, &sess, reuse);
}

/* Initialize the session with the first lists and sign with the second. */
static void do_sign_other(char *sec_s, char *sk_s, char *m_s, char *agg_s, char *pks_s, char *msgs_s, char *nonces_s,
                          char *pks2_s, char *msgs2_s, char *nonces2_s) {
    unsigned char secb[64], sk[32], m[32];
    secp256k1_fullagg_session sess;
    int r;
    if (unhex(sec_s, secb, 64) != 64 || unhex(sk_s, sk, 32) != 32 || unhex(m_s, m, 32) != 32) {
        printf("SKIP\n"); return;
    }
    r = session(agg_s, pks_s, msgs_s, nonces_s, &sess);
    if (r < 0) { printf("SKIP\n"); return; }
    if (r == 0) { printf("FAIL\n"); return; }
    parse_list(pks2_s, 32, &pks_l);
    parse_list(msgs2_s, 32, &msgs_l);
    parse_list(nonces2_s, 66, &nonces_l);
    if (pks_l.bad_len || msgs_l.bad_len || nonces_l.bad_len) { printf("SKIP\n"); return; }
    if (pks_l.n != msgs_l.n || pks_l.n != nonces_l.n || pks_l.n == 0 || !load_pks() || !load_nonces()) {
        printf("FAIL\n"); return;
    }
    sign_loaded(secb, sk, m, &sess, 0);
}

static void do_sigagg(char *agg_s, char *pks_s, char *msgs_s, char *nonces_s, char *psigs_s) {
    secp256k1_fullagg_session sess;
    unsigned char sig[64];
    int r;
    parse_list(psigs_s, 32, &psigs_l);
    r = session(agg_s, pks_s, msgs_s, nonces_s, &sess);
    if (r < 0 || psigs_l.bad_len) { printf("SKIP\n"); return; }
    illegal = 0;
    if (r == 0 || !load_psigs() || !secp256k1_fullagg_partial_sig_agg(ctx, sig, &sess, psig_ptrs, (size_t)psigs_l.n) || illegal) {
        printf("FAIL\n"); return;
    }
    print_hex(sig, 64); printf("\n");
}

static void do_partial(char *psig_s, char *pks_s, char *msgs_s, char *nonces_s, char *i_s) {
    unsigned char pb[32];
    secp256k1_fullagg_partial_sig psig;
    parse_list(pks_s, 32, &pks_l);
    parse_list(msgs_s, 32, &msgs_l);
    parse_list(nonces_s, 66, &nonces_l);
    if (unhex(psig_s, pb, 32) != 32 || pks_l.bad_len || msgs_l.bad_len || nonces_l.bad_len) { printf("SKIP\n"); return; }
    if (pks_l.n != msgs_l.n || pks_l.n != nonces_l.n || pks_l.n == 0 || !load_pks() || !load_nonces()
        || !secp256k1_fullagg_partial_sig_parse(ctx, &psig, pb)) {
        printf("false\n"); return;
    }
    printf(secp256k1_fullagg_partial_sig_verify(ctx, &psig, nonce_ptrs, pk_ptrs, msg_ptrs, (size_t)pks_l.n, (size_t)atol(i_s)) ? "true\n" : "false\n");
}

static void do_verify(char *pks_s, char *msgs_s, char *sig_s) {
    unsigned char sig[64];
    parse_list(pks_s, 32, &pks_l);
    parse_list(msgs_s, 32, &msgs_l);
    if (unhex(sig_s, sig, 64) != 64 || pks_l.bad_len || msgs_l.bad_len) { printf("SKIP\n"); return; }
    if (pks_l.n != msgs_l.n || !load_pks()) { printf("false\n"); return; }
    printf(secp256k1_fullagg_verify(ctx, sig, pk_ptrs, msg_ptrs, (size_t)pks_l.n) ? "true\n" : "false\n");
}

/* The BIP's tweaks, with the library's general tweak functions. */
static void do_tweak(char *sk_s, char *t_s, char *xonly_s) {
    unsigned char sk[32], t[32], out[33];
    size_t len = 33;
    secp256k1_keypair kp;
    secp256k1_pubkey pub;
    if (unhex(sk_s, sk, 32) != 32 || unhex(t_s, t, 32) != 32) { printf("SKIP\n"); return; }
    if (!secp256k1_keypair_create(ctx, &kp, sk)) { printf("FAIL\n"); return; }
    if (xonly_s[0] == '1') {
        if (!secp256k1_keypair_xonly_tweak_add(ctx, &kp, t)) { printf("FAIL\n"); return; }
        secp256k1_keypair_sec(ctx, sk, &kp);
        secp256k1_keypair_pub(ctx, &pub, &kp);
    } else {
        int a, b;
        secp256k1_keypair_pub(ctx, &pub, &kp);
        a = secp256k1_ec_seckey_tweak_add(ctx, sk, t);
        b = secp256k1_ec_pubkey_tweak_add(ctx, &pub, t);
        if (a != b) { printf("MIXED\n"); return; }
        if (!a) { printf("FAIL\n"); return; }
    }
    secp256k1_ec_pubkey_serialize(ctx, out, &len, &pub, SECP256K1_EC_COMPRESSED);
    print_hex(sk, 32); printf(":"); print_hex(out, 33); printf("\n");
}

int main(void) {
    secp256k1_context *c = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
    static char line[1 << 16];
    secp256k1_context_set_illegal_callback(c, on_illegal, NULL);
    ctx = c;
    while (fgets(line, sizeof(line), stdin) != NULL) {
        char *save, *f[13];
        int k = 0;
        line[strcspn(line, "\n")] = 0;
        for (f[0] = strtok_r(line, " ", &save); f[k] != NULL && k < 12; f[k] = strtok_r(NULL, " ", &save)) k++;
        if (k == 4 && f[0][0] == 'G') do_noncegen(f[1], f[2], f[3]);
        else if (k == 4 && f[0][0] == 'C') do_noncegen_counter(f[1], f[2], f[3]);
        else if (k == 2 && f[0][0] == 'N') do_nonceagg(f[1]);
        else if (k == 8 && f[0][0] == 'S') do_sign(f[1], f[2], f[3], f[4], f[5], f[6], f[7], 0);
        else if (k == 8 && f[0][0] == 'R') do_sign(f[1], f[2], f[3], f[4], f[5], f[6], f[7], 1);
        else if (k == 11 && f[0][0] == 'X') do_sign_other(f[1], f[2], f[3], f[4], f[5], f[6], f[7], f[8], f[9], f[10]);
        else if (k == 6 && f[0][0] == 'A') do_sigagg(f[1], f[2], f[3], f[4], f[5]);
        else if (k == 6 && f[0][0] == 'P') do_partial(f[1], f[2], f[3], f[4], f[5]);
        else if (k == 4 && f[0][0] == 'V') do_verify(f[1], f[2], f[3]);
        else if (k == 4 && f[0][0] == 'T') do_tweak(f[1], f[2], f[3]);
        else printf("BADLINE\n");
        fflush(stdout);
    }
    secp256k1_context_destroy(c);
    return 0;
}
