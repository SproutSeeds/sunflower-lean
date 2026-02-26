/-
  SAT Encoding Bridge for M(n,3) Upper Bounds

  Self-contained SAT encoding generated in Lean, verified via LRAT.
  The bridge has two components:

  1. Sunflower exclusion clauses: each 3-sunflower triple generates a clause
     ¬x_a ∨ ¬x_b ∨ ¬x_c (SF-free families satisfy all such clauses)

  2. Sequential counter (atmost formulation): encodes
     "at least B of the 2^n variables are true"

  Pipeline:
  - Lean computes sunflowerCNF n B (deterministic, auditable)
  - CaDiCaL proves UNSAT with LRAT certificate (external)
  - Lean verifies LRAT via native_decide (kernel-level trust)
  - Bridge theorem: UNSAT → ∀ SF-free F, |F| < B

  Authors: Cody Mitchell, Claude (Opus)
  Date: February 2026
-/

import SunflowerLean.SmallCases
import SunflowerLean.SATNative

open Std.Sat
open Std.Tactic.BVDecide.LRAT

namespace SunflowerLean

-- ============================================================================
-- Bitmask ↔ Subset bijection
-- ============================================================================

/-- Convert a bitmask (natural number) to a subset of Fin n.
    Bit j is set iff j ∈ the subset. -/
def bitmaskToSubset (n : Nat) (m : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun j => (m >>> j.val) &&& 1 = 1

/-- Convert a subset of Fin n to its bitmask representation. -/
def subsetToBitmask (s : Finset (Fin n)) : Nat :=
  s.fold (· ||| ·) 0 fun j => 1 <<< j.val

-- ============================================================================
-- Sunflower triple detection
-- ============================================================================

/-- Check if three subsets form a 3-sunflower
    (all pairwise intersections equal). -/
def isSunflowerTriple' [DecidableEq α] (A B C : Finset α) : Bool :=
  A ∩ B = A ∩ C && A ∩ B = B ∩ C

/-- Enumerate all 3-sunflower triples among subsets of Fin n
    (by bitmask index). Returns triples (a, b, c) with a < b < c.
    Pure functional definition for easier proof reasoning. -/
def sunflowerTriples (n : Nat) : List (Nat × Nat × Nat) :=
  let N := 2 ^ n
  (List.range N).flatMap fun a =>
    (List.range N).flatMap fun b =>
      if b > a then
        (List.range N).filterMap fun c =>
          if c > b &&
             isSunflowerTriple' (bitmaskToSubset n a)
               (bitmaskToSubset n b) (bitmaskToSubset n c) then
            some (a, b, c)
          else none
      else []

-- ============================================================================
-- Sunflower exclusion clauses (0-indexed variables)
-- ============================================================================

/-- Generate the sunflower exclusion clauses for Fin n.
    For each sunflower triple (a, b, c), clause: ¬x_a ∨ ¬x_b ∨ ¬x_c.
    Variables are 0-indexed. -/
def sunflowerClauses (n : Nat) : CNF Nat :=
  (sunflowerTriples n).map fun (a, b, c) =>
    [(a, false), (b, false), (c, false)]

-- ============================================================================
-- Sequential counter for "at least B of x₀,...,x_{N-1} are true"
-- Uses atmost(k false) formulation where k = N - B.
-- ============================================================================

/-- Auxiliary variable index in the sequential counter.
    Register s_{i,j} tracks "at least j+1 of x₀,...,xᵢ are FALSE".
    Column j holds registers for i = j, j+1, ..., N-1.
    Offset: column j starts at startIdx + j*N - j*(j-1)/2. -/
def seqCounterVar (N _K startIdx : Nat) (i j : Nat) : Nat :=
  let colOffset := j * N - j * (j - 1) / 2
  startIdx + colOffset + (i - j)

/-- Sequential counter clauses (atmost formulation).
    k = N - B: max number of false primary variables allowed.
    Register s_{i,j} = "at least j+1 of x₀,...,xᵢ are FALSE".
    Clause types:
    1. xᵢ ∨ s_{i,0}                     (false → register)
    2. ¬s_{i-1,j} ∨ s_{i,j}             (monotonicity)
    3. xᵢ ∨ ¬s_{i-1,j-1} ∨ s_{i,j}     (counting)
    4. xᵢ ∨ ¬s_{i-1,k-1}               (overflow block) -/
def seqCounterClauses (N B startIdx : Nat) : CNF Nat :=
  let k := N - B  -- max number of false variables allowed
  let s := seqCounterVar N k startIdx
  -- i = 0: x₀ ∨ s_{0,0}
  [[(0, true), (s 0 0, true)]] ++
  (List.range (N - 1)).flatMap fun i' =>
    let i := i' + 1
    let maxJ := min i (k - 1)
    -- Type 1: xᵢ ∨ s_{i,0}
    [[(i, true), (s i 0, true)]] ++
    -- Types 2+3 for each j ∈ [0, maxJ]
    ((List.range (maxJ + 1)).flatMap fun j =>
      -- Type 2 (monotonicity): ¬s_{i-1,j} ∨ s_{i,j}
      (if j < i then [[(s (i-1) j, false), (s i j, true)]] else []) ++
      -- Type 3 (counting): xᵢ ∨ ¬s_{i-1,j-1} ∨ s_{i,j}
      (if 0 < j then [[(i, true), (s (i-1) (j-1), false), (s i j, true)]]
       else [])) ++
    -- Type 4 (overflow block): xᵢ ∨ ¬s_{i-1,k-1}
    (if k > 0 && i ≥ k then [[(i, true), (s (i-1) (k-1), false)]]
     else [])

-- ============================================================================
-- Complete CNF encoding
-- ============================================================================

/-- The complete CNF encoding for
    "does a B-element 3-SF-free family on Fin n exist?"
    Variables 0..2^n-1: one per subset (by bitmask).
    Variables 2^n..: sequential counter auxiliaries. -/
def sunflowerCNF (n B : Nat) : CNF Nat :=
  sunflowerClauses n ++ seqCounterClauses (2 ^ n) B (2 ^ n)

-- ============================================================================
-- LRAT verification: M(5,3) — self-contained
-- ============================================================================

/-- LRAT proof that sunflowerCNF 5 13 is UNSAT
    (CaDiCaL --plain --lrat, 253KB certificate). -/
def m5_bridge_lrat : Array IntAction :=
  match parseLRATProof (include_str "sat_m5_3_lean.lrat").toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

/-- Native LRAT verification for the Lean-generated n=5 CNF. -/
def m5_bridge_verified : Bool :=
  check m5_bridge_lrat (sunflowerCNF 5 13)

/-- The LRAT checker confirms sunflowerCNF 5 13 is UNSAT. -/
theorem m5_bridge_verified_eq_true :
    m5_bridge_verified = true := by native_decide

/-- sunflowerCNF 5 13 is unsatisfiable (kernel-verified). -/
theorem sunflowerCNF_5_13_unsat :
    (sunflowerCNF 5 13).Unsat :=
  check_sound m5_bridge_lrat (sunflowerCNF 5 13) m5_bridge_verified_eq_true

-- ============================================================================
-- Canonical register assignment
-- ============================================================================

/-- Count how many of σ(0),...,σ(i) are FALSE. -/
def countFalse (σ : Nat → Bool) (i : Nat) : Nat :=
  (List.range (i + 1)).filter (fun k => !σ k) |>.length

/-- Search columns 0..k-1 to find which column contains the auxiliary
    variable at offset `aux` from startIdx. Returns (i, j). -/
private def findColumn (N k aux j colStart : Nat) : Nat × Nat :=
  if j ≥ k then (0, 0)
  else if aux < colStart + (N - j) then (j + (aux - colStart), j)
  else findColumn N k aux (j + 1) (colStart + (N - j))
termination_by k - j
decreasing_by omega

/-- Given σ on primary variables, extend to sequential counter registers.
    s_{i,j} = true iff countFalse(σ, i) ≥ j+1.
    k = N - B is the max false count. -/
def canonicalExtension
    (σ : Nat → Bool) (N B startIdx : Nat) : Nat → Bool :=
  fun v =>
    if v < N then σ v
    else
      let k := N - B
      let totalAux := k * N - k * (k - 1) / 2
      if v < startIdx || v ≥ startIdx + totalAux then
        false  -- out of range
      else
        -- Decode (v - startIdx) to (i, j) using column layout
        let aux := v - startIdx
        let (i, j) := findColumn N k aux 0 0
        decide (countFalse σ i ≥ j + 1)

-- ============================================================================
-- Helper: canonical extension agrees on primary variables
-- ============================================================================

theorem canonicalExtension_primary (σ : Nat → Bool)
    (N B : Nat) (v : Nat) (hv : v < N) :
    canonicalExtension σ N B N v = σ v := by
  simp [canonicalExtension, hv]

-- ============================================================================
-- Helper: |F| ≥ B → countFalse ≤ 2^n - B
-- ============================================================================

/-- Inverse bitmask: subset → Nat via Nat.ofBits. -/
private def toMask (S : Finset (Fin n)) : Nat :=
  Nat.ofBits (fun i : Fin n => decide (i ∈ S))

/-- toMask produces bitmasks in range [0, 2^n). -/
private theorem toMask_lt (S : Finset (Fin n)) : toMask S < 2 ^ n :=
  Nat.ofBits_lt_two_pow _

/-- The bitmask filter test (m >>> j) &&& 1 = 1 is equivalent to testBit. -/
private lemma bitmask_test_iff (m j : Nat) :
    ((m >>> j) &&& 1 = 1) ↔ (m.testBit j = true) := by
  -- Show (m >>> j) &&& 1 = (m.testBit j).toNat via bit-extensionality
  suffices h : (m >>> j) &&& 1 = (m.testBit j).toNat by
    rw [h]; cases m.testBit j <;> simp
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_shiftRight]
  cases k with
  | zero =>
    have h1 : (1 : Nat).testBit 0 = true := by native_decide
    rw [show j + 0 = j from by omega, h1, Bool.and_true]
    cases m.testBit j <;> native_decide
  | succ k =>
    have h_exp : 1 < 2 ^ (k + 1) :=
      one_lt_pow₀ (by omega : (1 : Nat) < 2) (by omega : k + 1 ≠ 0)
    have h1 : (1 : Nat).testBit (k + 1) = false :=
      Nat.testBit_lt_two_pow h_exp
    have h2 : ((Nat.testBit m j).toNat).testBit (k + 1) = false := by
      apply Nat.testBit_lt_two_pow
      cases Nat.testBit m j <;> simp
    simp [h1, h2]

/-- Round-trip: bitmaskToSubset ∘ toMask = id. -/
private theorem bitmaskToSubset_toMask (S : Finset (Fin n)) :
    bitmaskToSubset n (toMask S) = S := by
  ext j
  simp only [bitmaskToSubset, Finset.mem_filter, Finset.mem_univ, true_and, toMask]
  rw [bitmask_test_iff]
  rw [Nat.testBit_ofBits_lt _ _ j.isLt]
  simp [Fin.eta]

/-- toMask is injective (follows from round-trip). -/
private theorem toMask_injective : Function.Injective (toMask (n := n)) := by
  intro S T h
  have := congr_arg (bitmaskToSubset n) h
  rw [bitmaskToSubset_toMask, bitmaskToSubset_toMask] at this
  exact this

/-- bitmaskToSubset is injective on [0, 2^n):
    distinct bitmasks in range give distinct subsets. -/
private theorem bitmaskToSubset_ne (a b : Nat)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
    bitmaskToSubset n a ≠ bitmaskToSubset n b := by
  intro heq
  apply hab
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have h := Finset.ext_iff.mp heq ⟨k, hk⟩
    simp only [bitmaskToSubset, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rwa [bitmask_test_iff, bitmask_test_iff, ← Bool.eq_iff_iff] at h
  · push_neg at hk
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hk)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hk))]

/-- Extract full properties from sunflowerTriples membership. -/
private theorem sunflowerTriples_spec (n : Nat) (a b c : Nat)
    (h : (a, b, c) ∈ sunflowerTriples n) :
    a < b ∧ b < c ∧
    isSunflowerTriple' (bitmaskToSubset n a) (bitmaskToSubset n b)
      (bitmaskToSubset n c) = true := by
  simp only [sunflowerTriples, List.mem_flatMap, List.mem_range] at h
  obtain ⟨a', ha', b', hb', hrest⟩ := h
  by_cases hab : b' > a'
  · simp only [hab, ↓reduceIte, List.mem_filterMap, List.mem_range] at hrest
    obtain ⟨c', _, hsome⟩ := hrest
    split at hsome
    · next hcond =>
      obtain ⟨rfl, rfl, rfl⟩ := hsome
      have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hcond
      exact ⟨hab, decide_eq_true_eq.mp h1, h2⟩
    · next _ => simp at hsome
  · simp only [show ¬(b' > a') from hab, ↓reduceIte, List.not_mem_nil] at hrest

/-- If F has at least B members and σ encodes membership via bitmask,
    then at most 2^n - B primary variables are false. -/
theorem countFalse_from_card (n B : Nat)
    (F : Finset (Finset (Fin n)))
    (hcard : F.card ≥ B)
    (σ : Nat → Bool)
    (hσ : ∀ i, σ i = decide (bitmaskToSubset n i ∈ F)) :
    countFalse σ (2 ^ n - 1) ≤ 2 ^ n - B := by
  unfold countFalse
  have hN : 2 ^ n ≥ 1 := Nat.one_le_two_pow
  rw [show 2 ^ n - 1 + 1 = 2 ^ n from by omega]
  -- Partition: true_count + false_count = N (by direct induction)
  have h_part : ∀ (l : List Nat),
      (l.filter σ).length + (l.filter (fun k => !σ k)).length = l.length := by
    intro l; induction l with
    | nil => simp [List.filter]
    | cons x xs ih =>
      simp only [List.filter]
      cases σ x <;> simp <;> omega
  have h_total := h_part (List.range (2 ^ n))
  rw [List.length_range] at h_total
  -- Suffices: true_count ≥ B
  suffices h_ge : B ≤ (List.filter σ (List.range (2 ^ n))).length by omega
  -- Injection: F ↪ {i < 2^n | σ i = true} via toMask
  have h_mem : ∀ S ∈ F, toMask S ∈ (List.range (2 ^ n)).filter σ := by
    intro S hS
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr (toMask_lt S),
           by rw [hσ, bitmaskToSubset_toMask]; simp [hS]⟩
  have h_nodup : ((List.range (2 ^ n)).filter σ).Nodup :=
    List.nodup_range.filter _
  have h_sub : F.image toMask ⊆ ((List.range (2 ^ n)).filter σ).toFinset := by
    intro i hi
    rw [List.mem_toFinset]
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hi
    exact h_mem S hS
  calc B
      ≤ F.card := hcard
    _ = (F.image toMask).card :=
        (Finset.card_image_of_injective F toMask_injective).symm
    _ ≤ ((List.range (2 ^ n)).filter σ).toFinset.card :=
        Finset.card_le_card h_sub
    _ = ((List.range (2 ^ n)).filter σ).length :=
        List.toFinset_card_of_nodup h_nodup

-- ============================================================================
-- Helper: sunflower triples have bounded indices
-- ============================================================================

/-- All triples from sunflowerTriples have components < 2^n.
    Follows directly from all components coming from List.range (2^n). -/
theorem sunflowerTriples_bound (n : Nat) (a b c : Nat)
    (h : (a, b, c) ∈ sunflowerTriples n) :
    a < 2 ^ n ∧ b < 2 ^ n ∧ c < 2 ^ n := by
  simp only [sunflowerTriples, List.mem_flatMap] at h
  obtain ⟨a', ha', b', hb', hrest⟩ := h
  rw [List.mem_range] at ha'
  rw [List.mem_range] at hb'
  by_cases hab : b' > a'
  · simp only [hab, ite_true, List.mem_filterMap] at hrest
    obtain ⟨c', hc', hsome⟩ := hrest
    rw [List.mem_range] at hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsome
    split at hsome <;> simp at hsome
    obtain ⟨rfl, rfl, rfl⟩ := hsome
    exact ⟨ha', hb', hc'⟩
  · simp only [hab, ite_false, List.not_mem_nil] at hrest

-- ============================================================================
-- Soundness: sunflower exclusion clauses
-- ============================================================================

/-- SF-free families satisfy all sunflower exclusion clauses.
    Each clause comes from a sunflower triple (a,b,c). If all three
    bitmask-subsets were in F, they'd form a 3-sunflower, contradicting
    IsSunflowerFree. Therefore ≥1 is not in F, making the clause true. -/
theorem sf_free_satisfies_clauses (n : Nat)
    (F : Finset (Finset (Fin n))) (hfree : IsSunflowerFree F 3)
    (σ : Nat → Bool)
    (hσ : ∀ i, σ i = decide (bitmaskToSubset n i ∈ F)) :
    ∀ cl ∈ sunflowerClauses n,
      CNF.Clause.eval σ cl = true := by
  intro cl hcl
  simp only [sunflowerClauses, List.mem_map] at hcl
  obtain ⟨⟨a, b, c⟩, hmem, rfl⟩ := hcl
  -- Clause: [(a, false), (b, false), (c, false)]
  -- Eval: (σ a == false) || (σ b == false) || (σ c == false)
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  -- Handle 7/8 cases by simp; the all-true case requires sunflower argument
  cases ha_val : σ a <;> cases hb_val : σ b <;> cases hc_val : σ c <;> simp
  -- Remaining: σ a = true, σ b = true, σ c = true → exfalso
  exfalso
  -- All three subsets are in F
  let A := bitmaskToSubset n a
  let B := bitmaskToSubset n b
  let C := bitmaskToSubset n c
  have hA : A ∈ F := by
    rw [show A = bitmaskToSubset n a from rfl]
    exact decide_eq_true_eq.mp (hσ a ▸ ha_val)
  have hB : B ∈ F :=
    decide_eq_true_eq.mp (hσ b ▸ hb_val)
  have hC : C ∈ F :=
    decide_eq_true_eq.mp (hσ c ▸ hc_val)
  -- Extract properties from sunflowerTriples membership
  have ⟨ha_bd, hb_bd, hc_bd⟩ := sunflowerTriples_bound n a b c hmem
  have ⟨hab_lt, hbc_lt, h_triple⟩ := sunflowerTriples_spec n a b c hmem
  -- Three subsets are pairwise distinct
  have hAB : A ≠ B := bitmaskToSubset_ne a b ha_bd hb_bd (by omega)
  have hAC : A ≠ C := bitmaskToSubset_ne a c ha_bd hc_bd (by omega)
  have hBC : B ≠ C := bitmaskToSubset_ne b c hb_bd hc_bd (by omega)
  -- Extract pairwise intersection equality from isSunflowerTriple'
  simp only [isSunflowerTriple', Bool.and_eq_true, decide_eq_true_eq] at h_triple
  obtain ⟨h_AC, h_BC⟩ := h_triple
  -- Construct the 3-sunflower subfamily {A, B, C}
  let sub : Finset (Finset (Fin n)) := {A, B, C}
  have h_sub_F : sub ⊆ F := by
    intro S hS
    simp only [sub, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl <;> assumption
  have h_card3 : sub.card = 3 := by
    have hA_notin : A ∉ ({B, C} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hAB, hAC⟩
    have hB_notin : B ∉ ({C} : Finset _) := by
      simp only [Finset.mem_singleton]
      exact hBC
    simp only [sub, Finset.card_insert_of_notMem hA_notin,
               Finset.card_insert_of_notMem hB_notin, Finset.card_singleton]
  have h_core : ∃ core : Finset (Fin n),
      ∀ S T : Finset (Fin n), S ∈ sub → T ∈ sub → S ≠ T → S ∩ T = core := by
    refine ⟨A ∩ B, ?_⟩
    intro S T hS hT hne
    simp only [sub, Finset.mem_insert, Finset.mem_singleton] at hS hT
    rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | rfl
      | exact Finset.inter_comm B A
      | exact h_AC.symm
      | exact h_BC.symm
      | (rw [Finset.inter_comm C A]; exact h_AC.symm)
      | (rw [Finset.inter_comm C B]; exact h_BC.symm)
  exact hfree sub h_sub_F ⟨h_card3, h_core⟩

-- ============================================================================
-- Soundness: sequential counter — helper lemmas
-- ============================================================================

/-- countFalse step: adding one more element. -/
private lemma countFalse_succ (σ : Nat → Bool) (i : Nat) :
    countFalse σ (i + 1) = countFalse σ i + if σ (i + 1) then 0 else 1 := by
  simp only [countFalse, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil, List.length_nil]
  cases σ (i + 1) <;> simp

/-- countFalse is monotone (one step). -/
private lemma countFalse_mono (σ : Nat → Bool) (i : Nat) :
    countFalse σ i ≤ countFalse σ (i + 1) := by
  rw [countFalse_succ]; omega

/-- If σ(i+1) is false, countFalse increases by 1. -/
private lemma countFalse_step_false (σ : Nat → Bool) (i : Nat) (h : σ (i + 1) = false) :
    countFalse σ (i + 1) = countFalse σ i + 1 := by
  rw [countFalse_succ]; simp [h]

/-- countFalse is monotone for any gap. -/
private lemma countFalse_le_of_le (σ : Nat → Bool) {i j : Nat} (h : i ≤ j) :
    countFalse σ i ≤ countFalse σ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ n ih =>
    calc countFalse σ i ≤ countFalse σ (i + n) := ih (by omega)
      _ ≤ countFalse σ (i + n + 1) := countFalse_mono σ (i + n)

/-- If σ i is false, then countFalse σ i ≥ 1. -/
private lemma countFalse_pos_of_false (σ : Nat → Bool) (i : Nat) (h : σ i = false) :
    countFalse σ i ≥ 1 := by
  induction i with
  | zero =>
    simp [countFalse, List.range_succ, List.range_zero, List.filter_cons,
      List.filter_nil, h]
  | succ n ih =>
    have hm := countFalse_mono σ n
    rw [countFalse_succ]
    cases hσn : σ n with
    | false => have := ih hσn; omega
    | true => simp [h]

/-- Cumulative column start in the sequential counter layout.
    Column c starts at offset colStartFn N c from startIdx. -/
private def colStartFn (N : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => colStartFn N c + (N - c)

/-- colStartFn is strictly monotone for c < N. -/
private lemma colStartFn_lt_succ (N c : Nat) (hc : c < N) :
    colStartFn N c < colStartFn N (c + 1) := by
  simp [colStartFn]; omega

/-- colStartFn is monotone for c ≤ c'. -/
private lemma colStartFn_mono {N : Nat} {c c' : Nat}
    (h : c ≤ c') (hc' : c' ≤ N) :
    colStartFn N c ≤ colStartFn N c' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  revert hc'
  induction d with
  | zero => intro; simp
  | succ n ih =>
    intro hc'
    calc colStartFn N c ≤ colStartFn N (c + n) := ih (by omega)
      _ ≤ colStartFn N (c + n + 1) := by simp [colStartFn]

/-- Key arithmetic: product of consecutive naturals is even. -/
private lemma consec_prod_even (j : Nat) : j * (j - 1) % 2 = 0 := by
  rcases j with _ | n
  · simp
  · simp only [Nat.succ_sub_one]
    -- Goal: (n + 1) * n % 2 = 0
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n = k + k (even): (k+k+1)*(k+k) = 2 * (k * (k+k+1))
      subst hk
      have : (k + k + 1) * (k + k) = 2 * (k * (k + k + 1)) := by ring
      rw [this]; exact Nat.mul_mod_right 2 _
    · -- n = 2*k + 1 (odd): (2*k+2)*(2*k+1) = 2 * ((k+1)*(2*k+1))
      subst hk
      have : (2 * k + 1 + 1) * (2 * k + 1) = 2 * ((k + 1) * (2 * k + 1)) := by ring
      rw [this]; exact Nat.mul_mod_right 2 _

/-- Closed form for colStartFn. -/
private lemma colStartFn_eq (N j : Nat) (hj : j ≤ N) :
    colStartFn N j = j * N - j * (j - 1) / 2 := by
  induction j with
  | zero => simp [colStartFn]
  | succ j ih =>
    simp only [colStartFn]
    rw [ih (by omega)]
    -- Goal: j * N - j * (j - 1) / 2 + (N - j) = (j + 1) * N - (j + 1) * j / 2
    -- Key relation: (j+1)*j/2 = j*(j-1)/2 + j (consecutive triangular numbers differ by j)
    have hqp : (j + 1) * j / 2 = j * (j - 1) / 2 + j := by
      have := Nat.div_add_mod (j * (j - 1)) 2
      have := consec_prod_even j
      have := Nat.div_add_mod ((j + 1) * j) 2
      have := consec_prod_even (j + 1)
      have : (j + 1) * j = j * (j - 1) + 2 * j := by
        rcases j with _ | n; · simp
        · simp only [show n + 1 - 1 = n from by omega]; ring
      omega
    have h_mul : (j + 1) * N = j * N + N := by ring
    have hp_le : j * (j - 1) / 2 ≤ j * N := by
      calc j * (j - 1) / 2 ≤ j * (j - 1) := Nat.div_le_self _ 2
        _ ≤ j * N := Nat.mul_le_mul_left j (by omega)
    -- Normalize (j+1)*(j+1-1) to (j+1)*j in the target
    simp only [show j + 1 - 1 = j from by omega]
    rw [hqp, h_mul]
    omega

/-- seqCounterVar offset from startIdx equals colStartFn + (i - j). -/
private lemma seqCounterVar_offset (N k i j : Nat)
    (hj : j ≤ i) (hi : i < N) (hk : j < k) (hkN : k ≤ N) :
    seqCounterVar N k N i j - N = colStartFn N j + (i - j) := by
  simp only [seqCounterVar]
  rw [colStartFn_eq N j (by omega)]
  omega

/-- totalAux = colStartFn N k (the total number of auxiliary variables). -/
private lemma totalAux_eq_colStartFn (N k : Nat) (hk : k ≤ N) :
    k * N - k * (k - 1) / 2 = colStartFn N k := by
  rw [colStartFn_eq N k hk]

/-- findColumn correctly decodes register variables.
    Starting at column c with running colStart = colStartFn N c,
    if the target is in column j₀ ≥ c, findColumn returns (i, j₀). -/
private lemma findColumn_spec (N k i j c : Nat)
    (hj : j < k) (hji : j ≤ i) (hi : i < N) (hk : k ≤ N)
    (hc : c ≤ j) :
    findColumn N k (colStartFn N j + (i - j)) c (colStartFn N c) = (i, j) := by
  unfold findColumn
  split
  · -- c ≥ k: impossible since c ≤ j < k
    omega
  · split
    · -- aux < colStart + (N - c): found in column c, so c = j
      rename_i _ h_hit
      have hcj : c = j := by
        by_contra hne
        have := colStartFn_mono (show c + 1 ≤ j by omega) (by omega : j ≤ N)
        have : colStartFn N c + (N - c) = colStartFn N (c + 1) := by simp [colStartFn]
        omega
      subst hcj; refine Prod.ext ?_ rfl; omega
    · -- aux ≥ colStart + (N - c): skip column c, recurse
      rename_i _ h_skip
      have hclt : c + 1 ≤ j := by
        by_contra hne
        have : c = j := by omega
        subst this; omega
      have hcs : colStartFn N c + (N - c) = colStartFn N (c + 1) := by
        simp [colStartFn]
      rw [hcs]
      exact findColumn_spec N k i j (c + 1) hj hji hi hk hclt
termination_by k - c

/-- seqCounterVar maps to a valid (in-range) auxiliary variable. -/
private lemma seqCounterVar_ge_N (N k i j : Nat) (hji : j ≤ i) :
    seqCounterVar N k N i j ≥ N := by
  simp [seqCounterVar]; omega

private lemma seqCounterVar_lt_bound (N k i j : Nat)
    (hj : j < k) (hji : j ≤ i) (hi : i < N) (hk : k ≤ N) :
    seqCounterVar N k N i j < N + (k * N - k * (k - 1) / 2) := by
  have h1 := seqCounterVar_offset N k i j hji hi hj hk
  have h2 : colStartFn N j + (i - j) < colStartFn N k := by
    calc colStartFn N j + (i - j) < colStartFn N j + (N - j) := by omega
      _ = colStartFn N (j + 1) := by simp [colStartFn]
      _ ≤ colStartFn N k := colStartFn_mono (by omega) (by omega)
  rw [totalAux_eq_colStartFn N k hk]
  omega

/-- canonicalExtension on a valid register variable returns the
    correct countFalse predicate.
    This is the key decoding lemma — it shows findColumn inverts seqCounterVar. -/
private lemma canon_register (σ : Nat → Bool) (N B : Nat)
    (i j : Nat) (hj : j < N - B) (hji : j ≤ i) (hi : i < N) :
    canonicalExtension σ N B N (seqCounterVar N (N - B) N i j) =
      decide (countFalse σ i ≥ j + 1) := by
  set k := N - B with hk_def
  set v := seqCounterVar N k N i j with hv_def
  have hv_ge : v ≥ N := seqCounterVar_ge_N N k i j hji
  have hv_lt : v < N + (k * N - k * (k - 1) / 2) :=
    seqCounterVar_lt_bound N k i j hj hji hi (by omega)
  -- findColumn inverts seqCounterVar
  have h_decode : findColumn N k (v - N) 0 0 = (i, j) := by
    have h_offset := seqCounterVar_offset N k i j hji hi hj (by omega)
    rw [h_offset]
    have h_fc := findColumn_spec N k i j 0 hj hji hi (by omega) (by omega)
    simp only [colStartFn] at h_fc
    exact h_fc
  -- Unfold canonicalExtension and resolve branches via split
  show canonicalExtension σ N B N v = _
  unfold canonicalExtension
  split
  · -- v < N: contradicts hv_ge
    omega
  · -- v ≥ N: beta-reduce have bindings, then split inner if
    dsimp only []
    split
    · -- Out of range (|| condition true): contradicts bounds
      rename_i _ h_oor
      exfalso
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h_oor
      rcases h_oor with h_lt | h_ge
      · exact absurd h_lt (by omega)
      · rw [show N - B = k from hk_def.symm] at h_ge; omega
    · -- Decode branch: findColumn gives (i, j)
      conv_lhs => rw [show N - B = k from hk_def.symm]
      simp only [h_decode]

-- ============================================================================
-- Helper: canonical extension returns false for out-of-range aux vars
-- ============================================================================

/-- When N ≤ B (k=0), all auxiliary variables are out of range,
    so canonicalExtension returns false for any v ≥ N. -/
private lemma canonicalExtension_aux_false (σ : Nat → Bool) (N B : Nat) (v : Nat)
    (hNB : N ≤ B) (hv : v ≥ N) :
    canonicalExtension σ N B N v = false := by
  unfold canonicalExtension
  rw [if_neg (show ¬(v < N) by omega)]
  simp [show N - B = 0 by omega, hv]

-- ============================================================================
-- Soundness: sequential counter
-- ============================================================================

/-- If at most N-B primary variables are false, canonical extension
    satisfies all sequential counter clauses.

    Proof outline: decompose clauses by type, then show each is satisfied:
    - Type 1 (xᵢ ∨ s_{i,0}): if σ(i) false, countFalse ≥ 1
    - Type 2 (¬s_{i-1,j} ∨ s_{i,j}): monotonicity of countFalse
    - Type 3 (xᵢ ∨ ¬s_{i-1,j-1} ∨ s_{i,j}): if σ(i) false, countFalse steps
    - Type 4 (xᵢ ∨ ¬s_{i-1,k-1}): overflow contradicts hcount -/
theorem seqCounter_sound (N B startIdx : Nat)
    (σ : Nat → Bool)
    (hcount : countFalse σ (N - 1) ≤ N - B)
    (hN : N > 0)
    (hstart : startIdx = N) :
    ∀ c ∈ seqCounterClauses N B startIdx,
      CNF.Clause.eval (canonicalExtension σ N B startIdx) c = true := by
  intro c hc
  rw [hstart] at hc ⊢
  -- k = N - B is the max false count. Either k > 0, or k = 0 (and all vars true).
  have hk_pos_or_zero : N - B > 0 ∨ (N ≤ B ∧ ∀ v, v < N → σ v = true) := by
    by_cases h : N - B > 0
    · left; exact h
    · right
      have hNB : N ≤ B := by omega
      refine ⟨hNB, ?_⟩
      have hk0 : N - B = 0 := by omega
      rw [hk0] at hcount
      intro v hv
      cases hσv : σ v with
      | true => rfl
      | false =>
        exfalso
        have h1 := countFalse_pos_of_false σ v hσv
        have h2 := countFalse_le_of_le σ (show v ≤ N - 1 by omega)
        omega
  -- We abbreviate for readability
  suffices ∀ c ∈ seqCounterClauses N B N,
      CNF.Clause.eval (canonicalExtension σ N B N) c = true from this c hc
  intro c hc
  simp only [seqCounterClauses] at hc
  rw [List.mem_append] at hc
  rcases hc with hc_init | hc_loop
  · -- INIT clause: [(0, true), (s 0 0, true)]
    rw [List.mem_singleton] at hc_init; subst hc_init
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
    by_cases h0 : σ 0 = true
    · have := canonicalExtension_primary σ N B 0 hN
      simp [this, h0]
    · rw [Bool.not_eq_true] at h0
      rcases hk_pos_or_zero with hk | ⟨hNB, hall⟩
      · have h_ce_0 := canonicalExtension_primary σ N B 0 hN
        simp [h_ce_0, h0]
        rw [canon_register σ N B 0 0 (by omega) (by omega) hN]
        simp [countFalse_pos_of_false σ 0 h0]
      · exact absurd (hall 0 hN) (by rw [h0]; decide)
  · -- LOOP clause: from (List.range (N-1)).flatMap f
    rw [List.mem_flatMap] at hc_loop
    obtain ⟨i', hi', hc_i⟩ := hc_loop
    rw [List.mem_range] at hi'
    set i := i' + 1 with hi_def
    have hi_lt : i < N := by omega
    -- Decompose: c ∈ ([type1] ++ inner_flatMap) ++ [type4?]
    rw [List.mem_append] at hc_i
    rcases hc_i with hc_left | hc_t4
    · -- Left: c ∈ [type1] ++ inner_flatMap
      rw [List.mem_append] at hc_left
      rcases hc_left with hc_t1 | hc_inner
      · -- TYPE 1: [(i, true), (s i 0, true)]
        rw [List.mem_singleton] at hc_t1; subst hc_t1
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
        by_cases hσi : σ i = true
        · have := canonicalExtension_primary σ N B i hi_lt
          simp [this, hσi]
        · rw [Bool.not_eq_true] at hσi
          rcases hk_pos_or_zero with hk | ⟨hNB, hall⟩
          · have h_ce := canonicalExtension_primary σ N B i hi_lt
            simp [h_ce, hσi]
            rw [canon_register σ N B i 0 (by omega) (by omega) hi_lt]
            simp [countFalse_pos_of_false σ i hσi]
          · exact absurd (hall i hi_lt) (by rw [hσi]; decide)
      · -- TYPES 2+3: from inner flatMap over j
        rw [List.mem_flatMap] at hc_inner
        obtain ⟨j, hj_mem, hc_j⟩ := hc_inner
        rw [List.mem_range] at hj_mem
        rw [List.mem_append] at hc_j
        rcases hc_j with hc_t2 | hc_t3
        · -- TYPE 2: ¬s_{i-1,j} ∨ s_{i,j}  (if j < i)
          split at hc_t2
          · next hjlt =>
            rw [List.mem_singleton] at hc_t2; subst hc_t2
            rcases hk_pos_or_zero with hk | ⟨hNB, hall⟩
            · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
              rw [canon_register σ N B (i-1) j (by omega) (by omega) (by omega),
                  canon_register σ N B i j (by omega) (by omega) hi_lt]
              simp only [Bool.or_eq_true, beq_iff_eq,
                decide_eq_false_iff_not, decide_eq_true_eq, not_le, ge_iff_le]
              by_cases h : countFalse σ (i - 1) ≥ j + 1
              · right; exact Nat.le_trans h (countFalse_mono σ (i - 1))
              · left; omega
            · -- k = 0: register vars are out-of-range → ¬false = true
              simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
              have hv1 : seqCounterVar N (N - B) N (i - 1) j ≥ N := by
                simp [seqCounterVar]; omega
              rw [canonicalExtension_aux_false σ N B _ hNB hv1]
              simp
          · simp at hc_t2
        · -- TYPE 3: xᵢ ∨ ¬s_{i-1,j-1} ∨ s_{i,j}  (if 0 < j)
          split at hc_t3
          · next hjpos =>
            rw [List.mem_singleton] at hc_t3; subst hc_t3
            rcases hk_pos_or_zero with hk | ⟨hNB, hall⟩
            · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
              by_cases hσi : σ i = true
              · have := canonicalExtension_primary σ N B i hi_lt
                simp [this, hσi]
              · rw [Bool.not_eq_true] at hσi
                rw [canonicalExtension_primary σ N B i hi_lt]
                simp [hσi]
                have hi1 : i - 1 + 1 = i := by omega
                rw [canon_register σ N B (i-1) (j-1) (by omega) (by omega) (by omega),
                    canon_register σ N B i j (by omega) (by omega) hi_lt]
                simp only [Bool.or_eq_true, beq_iff_eq,
                  decide_eq_false_iff_not, decide_eq_true_eq, not_le, ge_iff_le]
                by_cases h : countFalse σ (i - 1) ≥ j
                · right
                  have h_step := countFalse_step_false σ (i-1) (hi1 ▸ hσi)
                  rw [hi1] at h_step
                  omega
                · left; omega
            · -- k = 0: j < min i (k-1) + 1 with k=0 gives j=0, contradicting 0 < j
              exfalso; omega
          · simp at hc_t3
    · -- TYPE 4: xᵢ ∨ ¬s_{i-1,k-1}  (if k > 0 && i ≥ k)
      split at hc_t4
      · next hcond =>
        rw [List.mem_singleton] at hc_t4; subst hc_t4
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨hk_pos, hi_ge_k⟩ := hcond
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
        by_cases hσi : σ i = true
        · have := canonicalExtension_primary σ N B i hi_lt
          simp [this, hσi]
        · rw [Bool.not_eq_true] at hσi
          rw [canonicalExtension_primary σ N B i hi_lt]
          simp [hσi]
          rw [canon_register σ N B (i-1) (N - B - 1) (by omega) (by omega) (by omega)]
          simp only [Bool.or_eq_true, beq_iff_eq,
            decide_eq_false_iff_not, decide_eq_true_eq, not_le, ge_iff_le]
          -- countFalse σ (i-1) < k, because σ(i)=false means step +1,
          -- and monotonicity up to N-1 gives ≤ k, so i-1 count < k
          have hi1 : i - 1 + 1 = i := by omega
          have h_step := countFalse_step_false σ (i-1) (hi1 ▸ hσi)
          rw [hi1] at h_step
          have h_mono := countFalse_le_of_le σ (show i ≤ N - 1 by omega)
          omega
      · simp at hc_t4

-- ============================================================================
-- Helper: sunflower clause eval invariant under canonical extension
-- ============================================================================

/-- Sunflower clauses only use variables < 2^n.
    Since canonicalExtension agrees with σ on those,
    evaluation is preserved. -/
theorem sf_clause_eval_canonical (n B : Nat) (σ : Nat → Bool)
    (c : CNF.Clause Nat) (hc : c ∈ sunflowerClauses n) :
    CNF.Clause.eval (canonicalExtension σ (2 ^ n) B (2 ^ n)) c =
    CNF.Clause.eval σ c := by
  -- Extract the triple (a, b, c') from sunflowerClauses
  simp only [sunflowerClauses, List.mem_map] at hc
  obtain ⟨⟨a, b', c'⟩, hmem, rfl⟩ := hc
  -- Get bounds: a, b', c' < 2^n
  have ⟨ha, hb, hc'⟩ := sunflowerTriples_bound n a b' c' hmem
  -- Clause eval unfolds to: (f a == false) || (f b' == false) || ...
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  -- Rewrite canonicalExtension to σ on primary variables
  rw [canonicalExtension_primary σ (2 ^ n) B a ha,
      canonicalExtension_primary σ (2 ^ n) B b' hb,
      canonicalExtension_primary σ (2 ^ n) B c' hc']

-- ============================================================================
-- Bridge theorem (generic)
-- ============================================================================

/-- If sunflowerCNF n B is UNSAT, then every 3-SF-free family on Fin n
    has fewer than B members.

    Proof sketch:
    1. Assume F is 3-SF-free with |F| ≥ B
    2. Define σ(i) := (bitmaskToSubset n i ∈ F)
    3. σ' := canonicalExtension σ (extends to counter registers)
    4. σ' satisfies all sunflower clauses (by SF-freeness)
    5. |F| ≥ B → at most 2^n - B false vars → counter clauses satisfied
    6. Therefore CNF is satisfiable — contradicts UNSAT -/
theorem bridge (n B : Nat) (hB : B > 0) (hn : n > 0)
    (hunsat : (sunflowerCNF n B).Unsat) :
    ∀ F : Finset (Finset (Fin n)),
      IsSunflowerFree F 3 → F.card < B := by
  intro F hfree
  by_contra hge
  push_neg at hge
  -- Step 1: Construct assignment from F
  let σ : Nat → Bool := fun i => decide (bitmaskToSubset n i ∈ F)
  let N := 2 ^ n
  let σ' := canonicalExtension σ N B N
  -- Step 2: Show σ' satisfies sunflowerCNF n B
  have hsat : CNF.eval σ' (sunflowerCNF n B) = true := by
    -- sunflowerCNF = sunflowerClauses ++ seqCounterClauses
    show (sunflowerClauses n ++ seqCounterClauses N B N).all
      (fun c => CNF.Clause.eval σ' c) = true
    rw [List.all_append, Bool.and_eq_true]
    constructor
    · -- Sunflower exclusion clauses
      rw [List.all_eq_true]
      intro c hc
      rw [sf_clause_eval_canonical n B σ c hc]
      exact sf_free_satisfies_clauses n F hfree σ (fun i => rfl) c hc
    · -- Sequential counter clauses
      rw [List.all_eq_true]
      intro c hc
      have hcount := countFalse_from_card n B F hge σ (fun i => rfl)
      exact seqCounter_sound N B N σ hcount (by exact Nat.one_le_two_pow) rfl c hc
  -- Step 3: Contradiction with UNSAT
  have hfalse := hunsat σ'
  rw [hfalse] at hsat
  exact absurd hsat (by decide)

-- ============================================================================
-- Application: M(5,3) ≤ 12
-- ============================================================================

/-- M(5,3) ≤ 12: No 13-element 3-sunflower-free family on Fin 5 exists.
    Proof: Lean-generated CNF verified UNSAT via LRAT + bridge theorem.
    Bridge soundness proofs are pending formal verification. -/
theorem M_5_3_upper_bridge :
    ∀ F : Finset (Finset (Fin 5)),
      IsSunflowerFree F 3 → F.card ≤ 12 := by
  intro F hfree
  have h := bridge 5 13 (by omega) (by omega)
    sunflowerCNF_5_13_unsat F hfree
  omega

-- ============================================================================
-- LRAT verification: M(6,3) — self-contained
-- ============================================================================

/-- LRAT proof that sunflowerCNF 6 20 is UNSAT
    (CaDiCaL --plain --lrat, 26MB certificate, 2.3s solve). -/
def m6_bridge_lrat : Array IntAction :=
  match parseLRATProof (include_str "sat_m6_3_lean.lrat").toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

/-- Native LRAT verification for the Lean-generated n=6 CNF. -/
def m6_bridge_verified : Bool :=
  check m6_bridge_lrat (sunflowerCNF 6 20)

/-- The LRAT checker confirms sunflowerCNF 6 20 is UNSAT. -/
theorem m6_bridge_verified_eq_true :
    m6_bridge_verified = true := by native_decide

/-- sunflowerCNF 6 20 is unsatisfiable (kernel-verified). -/
theorem sunflowerCNF_6_20_unsat :
    (sunflowerCNF 6 20).Unsat :=
  check_sound m6_bridge_lrat (sunflowerCNF 6 20) m6_bridge_verified_eq_true

-- ============================================================================
-- Application: M(6,3) ≤ 19
-- ============================================================================

/-- M(6,3) ≤ 19: No 20-element 3-sunflower-free family on Fin 6 exists. -/
theorem M_6_3_upper_bridge :
    ∀ F : Finset (Finset (Fin 6)),
      IsSunflowerFree F 3 → F.card ≤ 19 := by
  intro F hfree
  have h := bridge 6 20 (by omega) (by omega)
    sunflowerCNF_6_20_unsat F hfree
  omega

end SunflowerLean
