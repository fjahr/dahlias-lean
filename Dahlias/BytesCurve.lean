import Dahlias.Bytes
import Dahlias.Correctness

/-!
# secp256k1 with 32-byte x-coordinates is a `Curve`

`secp256k1B` packages secp256k1 with x-coordinates as 32-byte arrays, the
encoding BIP 459 hashes and compares. Its operations are `specOps`, so every
theorem about `C.ops` holds for the byte-level algorithms.
-/

namespace Dahlias.Bytes

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors

/-! ## `bytes` and `int` are inverse -/

theorem toNat_toUInt8 (x : ℕ) : x.toUInt8.toNat = x % 256 := rfl

theorem toNatBE_cons (a : UInt8) (l : Bytes) :
    toNatBE (a :: l) = a.toNat * 256 ^ l.length + toNatBE l := by
  unfold toNatBE
  have h : ∀ (l : Bytes) (acc : ℕ),
      l.foldl (fun acc x => acc * 256 + x.toNat) acc =
        acc * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons, zero_mul, zero_add]
      rw [ih, ih b.toNat]
      ring
  simp only [List.foldl_cons, zero_mul, zero_add]
  exact h l a.toNat

theorem toNatBE_lt (l : Bytes) : toNatBE l < 256 ^ l.length := by
  induction l with
  | nil => simp [toNatBE]
  | cons a l ih =>
    rw [toNatBE_cons, List.length_cons, pow_succ]
    have := a.toNat_lt
    nlinarith

/-- `int` is injective on arrays of the same length. -/
theorem toNatBE_injective : ∀ {l l' : Bytes}, l.length = l'.length → toNatBE l = toNatBE l' →
    l = l'
  | [], [], _, _ => rfl
  | a :: l, a' :: l', hlen, h => by
    have hlen' : l.length = l'.length := by simpa using hlen
    rw [toNatBE_cons, toNatBE_cons, hlen'] at h
    have h1 := toNatBE_lt l
    have h2 := toNatBE_lt l'
    rw [hlen'] at h1
    have hpos : 0 < 256 ^ l'.length := by positivity
    have ha : a.toNat = a'.toNat := by
      have := congrArg (· / 256 ^ l'.length) h
      simpa [Nat.add_div_of_dvd_right, Nat.mul_add_div hpos, Nat.add_comm, Nat.div_eq_of_lt h1,
        Nat.div_eq_of_lt h2, Nat.add_mul_div_right _ _ hpos] using this
    rw [ha] at h
    rw [UInt8.toNat_inj.mp ha, toNatBE_injective hlen' (Nat.add_left_cancel h)]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

/-- The `k` low base-256 digits of `x`, most significant first. -/
def bytesK (k x : ℕ) : Bytes := (List.range k).reverse.map fun i => (x / 256 ^ i % 256).toUInt8

theorem bytes32_eq (x : ℕ) : bytes32 x = bytesK 32 x := rfl

@[simp] theorem length_bytesK (k x : ℕ) : (bytesK k x).length = k := by simp [bytesK]

theorem toNatBE_bytesK (k x : ℕ) : toNatBE (bytesK k x) = x % 256 ^ k := by
  induction k with
  | zero => simp [bytesK, toNatBE, Nat.mod_one]
  | succ k ih =>
    have : bytesK (k + 1) x = (x / 256 ^ k % 256).toUInt8 :: bytesK k x := by
      simp [bytesK, List.range_succ]
    rw [this, toNatBE_cons, ih, length_bytesK, pow_succ, Nat.mod_mul, toNat_toUInt8,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    ring

@[simp] theorem length_bytes32 (x : ℕ) : (bytes32 x).length = 32 := length_bytesK 32 x

theorem toNatBE_bytes32 {x : ℕ} (h : x < 2 ^ 256) : toNatBE (bytes32 x) = x := by
  rw [bytes32_eq, toNatBE_bytesK, Nat.mod_eq_of_lt (by norm_num; exact h)]

theorem bytes32_toNatBE {b : Bytes} (h : b.length = 32) : bytes32 (toNatBE b) = b := by
  refine toNatBE_injective (by simp [h]) ?_
  rw [bytes32_eq, toNatBE_bytesK, Nat.mod_eq_of_lt]
  simpa [h] using toNatBE_lt b

/-! ## The curve -/

theorem p_lt : p < 2 ^ 256 := by decide

/-- **secp256k1 with 32-byte x-coordinates.** -/
def secp256k1B : Curve n Point Bytes where
  G := G
  G_ne_zero := secp256k1.G_ne_zero
  order_G := n_smul_G
  x := xbytes
  hasEvenY := hasEvenY
  liftX := specOps.liftX
  x_neg P := by simp only [xbytes, Secp256k1.x_neg]
  hasEvenY_neg := hasEvenY_neg
  liftX_x P hP he := by
    have hv : (xCoord P).val < p := ZMod.val_lt _
    simp only [specOps, xbytes, length_bytes32, toNatBE_bytes32 (hv.trans p_lt), hv, and_self,
      ↓reduceIte, ZMod.natCast_zmod_val]
    exact Secp256k1.liftX_x P hP he
  liftX_spec r P h := by
    simp only [specOps] at h
    split_ifs at h with hr
    obtain ⟨h1, h2, h3⟩ := Secp256k1.liftX_spec _ P h
    refine ⟨h1, h2, ?_⟩
    rw [xbytes, h3, ZMod.val_natCast_of_lt hr.2, bytes32_toNatBE hr.1]

theorem secp256k1B_ops : secp256k1B.ops = specOps := rfl

end Dahlias.Bytes
