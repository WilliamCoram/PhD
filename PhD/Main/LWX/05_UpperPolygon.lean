/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«04_Halo»

/-!
# The upper bound polygon and [LWX, Lemma 4.1]

Pure `ℕ`-combinatorics of the exponent `λ` near the touching vertices `n_k = k·p·t`
([LWX, §3.23 Step II and §4]):

* `touchX p t k = k·p·t` — the `x`-coordinate `n_k` of the `k`-th touching vertex
  (`q = p` for `p` odd);
* `two_mul_lwxLambda_touchX` — [LWX, (3.23.1)]: `λ(n_k) = k²·p(p−1)t/2`;
* `lwxUpperTwice p t n` — twice the exponent of the **upper bound polygon** (the polygon with
  vertices `(n_k, λ(n_k))`, linear of slope `(k + ½)(p − 1)` on `[n_k, n_{k+1}]`), so that the
  upper polygon at `n` is `lwxUpperTwice p t n / 2`;
* `two_mul_lwxLambda_le_lwxUpperTwice`, `lwxUpperTwice_sub_two_mul_lwxLambda_le` —
  **[LWX, Lemma 4.1]**: `0 ≤ upper − lower ≤ (p² − 1)t/8` (in `v(T)`-units);
* the **band identities** [LWX, p. 25]: `λ(n_k ± i) = λ(n_k) ± k(p−1)·i` for `i ≤ t`, with
  strict excess `≥ |i| − t` beyond the band.
-/

open Finset

namespace LWX

/-! ### The touching vertices and block sums -/

/-- `n_k = k·p·t`, the `x`-coordinate of the `k`-th touching vertex ([LWX, §3.23]:
`n_k = kqt`, `q = p`). -/
def touchX (p t k : ℕ) : ℕ := k * (p * t)

/-- Summing a function of `⌊i/t⌋` over `i < m·t` counts each block `t` times. -/
theorem sum_range_mul_div (t m : ℕ) (ht : 0 < t) (f : ℕ → ℕ) :
    ∑ i ∈ range (m * t), f (i / t) = t * ∑ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have h : ∀ i ∈ range t, f ((m * t + i) / t) = f m := fun i hi ↦ by
      rw [mul_comm m t, Nat.mul_add_div ht, Nat.div_eq_of_lt (Finset.mem_range.1 hi), add_zero]
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Floor shift: `⌊(n_k + i)/t⌋ = kp + ⌊i/t⌋`. -/
theorem touchX_add_div (p t k i : ℕ) (ht : 0 < t) :
    (touchX p t k + i) / t = k * p + i / t := by
  rw [touchX, ← mul_assoc, mul_comm (k * p) t, Nat.mul_add_div ht]

/-- Floor shift within a block: `⌊(n_k + i)/(pt)⌋ = k` for `i < pt`. -/
theorem touchX_add_div_mul (p t k i : ℕ) (hpt : 0 < p * t) (hi : i < p * t) :
    (touchX p t k + i) / (p * t) = k := by
  rw [touchX, mul_comm k, Nat.mul_add_div hpt, Nat.div_eq_of_lt hi, add_zero]

/-- **[LWX, (3.23.1)]**: `λ(n_k) = k²·p(p−1)t/2`. -/
theorem two_mul_lwxLambda_touchX (p t k : ℕ) :
    2 * lwxLambda p t (touchX p t k) = k ^ 2 * p * (p - 1) * t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [touchX, lwxLambda]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [touchX, lwxLambda]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [touchX, lwxLambda]
  have hle : ∀ i ∈ range (touchX p t k), i / (p * t) ≤ i / t := fun i _ ↦
    Nat.div_le_div_left (Nat.le_mul_of_pos_left t hp) ht
  have hsplit : lwxLambda p t (touchX p t k) + ∑ i ∈ range (touchX p t k), i / (p * t) =
      ∑ i ∈ range (touchX p t k), i / t := by
    rw [lwxLambda, Finset.sum_tsub_distrib _ hle]
    exact Nat.sub_add_cancel (Finset.sum_le_sum hle)
  have h1 : ∑ i ∈ range (touchX p t k), i / t = t * ∑ j ∈ range (k * p), j := by
    have := sum_range_mul_div t (k * p) ht (fun j ↦ j)
    simpa [touchX, mul_assoc] using this
  have h2 : ∑ i ∈ range (touchX p t k), i / (p * t) = p * t * ∑ j ∈ range k, j := by
    have := sum_range_mul_div (p * t) k (Nat.mul_pos hp ht) (fun j ↦ j)
    simpa [touchX] using this
  have g1 := Finset.sum_range_id_mul_two (k * p)
  have g2 := Finset.sum_range_id_mul_two k
  have key : 2 * lwxLambda p t (touchX p t k) + p * t * (k * (k - 1)) =
      t * (k * p * (k * p - 1)) := by
    calc 2 * lwxLambda p t (touchX p t k) + p * t * (k * (k - 1))
        = 2 * lwxLambda p t (touchX p t k) + p * t * ((∑ j ∈ range k, j) * 2) := by rw [g2]
      _ = 2 * (lwxLambda p t (touchX p t k) + ∑ i ∈ range (touchX p t k), i / (p * t)) := by
          rw [h2]; ring
      _ = 2 * (t * ∑ j ∈ range (k * p), j) := by rw [hsplit, h1]
      _ = t * ((∑ j ∈ range (k * p), j) * 2) := by ring
      _ = t * (k * p * (k * p - 1)) := by rw [g1]
  have hkp : 1 ≤ k * p := Nat.mul_pos hk hp
  zify [hk, hp, hkp] at key ⊢
  linear_combination key

/-! ### The upper bound polygon -/

/-- Twice the exponent of the upper bound polygon of [LWX, §4]: the polygon with vertices
`(n_k, λ(n_k))` has slope `(k + ½)(p − 1)` on `[n_k, n_{k+1}]`, so its value at `n` is
`(∑_{i<n} (2⌊i/(pt)⌋ + 1)(p − 1)) / 2`. -/
def lwxUpperTwice (p t n : ℕ) : ℕ := ∑ i ∈ range n, (2 * (i / (p * t)) + 1) * (p - 1)

/-- The upper polygon is linear on each block `[n_k, n_{k+1}]`, with slope `(2k+1)(p−1)/2`. -/
theorem lwxUpperTwice_touchX_add (p t k x : ℕ) (hx : x ≤ p * t) :
    lwxUpperTwice p t (touchX p t k + x) =
      lwxUpperTwice p t (touchX p t k) + x * ((2 * k + 1) * (p - 1)) := by
  rw [lwxUpperTwice, lwxUpperTwice, Finset.sum_range_add]
  congr 1
  rcases Nat.eq_zero_or_pos (p * t) with h0 | hpt
  · obtain rfl : x = 0 := by omega
    simp
  · have h : ∀ i ∈ range x, (2 * ((touchX p t k + i) / (p * t)) + 1) * (p - 1) =
        (2 * k + 1) * (p - 1) := fun i hi ↦ by
      rw [touchX_add_div_mul p t k i hpt (lt_of_lt_of_le (Finset.mem_range.1 hi) hx)]
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The upper polygon passes through the touching vertices `(n_k, λ(n_k))`. -/
theorem lwxUpperTwice_touchX (p t k : ℕ) :
    lwxUpperTwice p t (touchX p t k) = 2 * lwxLambda p t (touchX p t k) := by
  induction k with
  | zero => simp [touchX, lwxUpperTwice, lwxLambda]
  | succ k ih =>
    have e : touchX p t (k + 1) = touchX p t k + p * t := by
      rw [touchX, touchX, Nat.succ_mul]
    rw [e, lwxUpperTwice_touchX_add p t k (p * t) le_rfl, ih, ← e, two_mul_lwxLambda_touchX,
      two_mul_lwxLambda_touchX]
    ring

/-- The block difference `2·(upper − lower)` at `n_k + x` is the signed sum
`∑_{i<x} ((p − 1) − 2⌊i/t⌋)` ([LWX, Lemma 4.1 proof]: "looking at the incremental differences
of slopes built from the vertex `(n_k, λ(n_k)v(T))`"). -/
theorem lwxUpperTwice_sub_two_mul_lwxLambda_eq (p t k x : ℕ) (ht : 0 < t) (hx : x ≤ p * t) :
    (lwxUpperTwice p t (touchX p t k + x) : ℤ) - 2 * lwxLambda p t (touchX p t k + x) =
      ∑ i ∈ range x, ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : x = 0 := by omega
    simp [touchX, lwxUpperTwice, lwxLambda]
  have hpt : 0 < p * t := Nat.mul_pos hp ht
  have hp1 : 1 ≤ p := hp
  have hlam : lwxLambda p t (touchX p t k + x) = lwxLambda p t (touchX p t k) +
      ∑ i ∈ range x, ((touchX p t k + i) / t - (touchX p t k + i) / (p * t)) := by
    rw [lwxLambda, lwxLambda, Finset.sum_range_add]
  have hterm : ∀ i ∈ range x,
      ((touchX p t k + i) / t - (touchX p t k + i) / (p * t) : ℕ) = k * (p - 1) + i / t :=
    fun i hi ↦ by
      rw [touchX_add_div p t k i ht,
        touchX_add_div_mul p t k i hpt (lt_of_lt_of_le (Finset.mem_range.1 hi) hx),
        Nat.mul_sub_one]
      have : k * p - k + k = k * p := Nat.sub_add_cancel (Nat.le_mul_of_pos_right k hp)
      generalize i / t = d
      omega
  rw [lwxUpperTwice_touchX_add p t k x hx, lwxUpperTwice_touchX, hlam,
    Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast [Nat.cast_sub hp1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- The signed block sum is nonnegative on a block. -/
theorem sum_block_nonneg (p t x : ℕ) (ht : 0 < t) (hx : x ≤ p * t) :
    0 ≤ ∑ i ∈ range x, ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : x = 0 := by omega
    simp
  have hp1 : 1 ≤ p := hp
  have htot : ∑ i ∈ range (p * t), ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) = 0 := by
    have h1 : (∑ i ∈ range (p * t), i / t : ℕ) = t * ∑ j ∈ range p, j := by
      simpa using sum_range_mul_div t p ht (fun j ↦ j)
    have g := Finset.sum_range_id_mul_two p
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have h1' : (∑ i ∈ range (p * t), ((i / t : ℕ) : ℤ)) = (t : ℤ) * ∑ j ∈ range p, (j : ℤ) := by
      have := congrArg (fun n : ℕ ↦ (n : ℤ)) h1
      simp only [Nat.cast_sum, Nat.cast_mul] at this
      exact this
    have g' : (∑ j ∈ range p, (j : ℤ)) * 2 = (p : ℤ) * ((p : ℤ) - 1) := by
      zify [hp1] at g
      exact g
    rw [h1']
    push_cast
    linear_combination (-(t : ℤ)) * g'
  -- the threshold `(p + 1) / 2 * t`: terms are nonnegative below it, nonpositive above it
  set q := (p + 1) / 2 with hq
  have hpos : ∀ i, i < q * t → 0 ≤ (p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ) := fun i hi ↦ by
    have hd : i / t < q := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    set d := i / t with hdef
    have h2 : 2 * d ≤ p - 1 := by omega
    have h3 : (2 * d : ℤ) ≤ (p : ℤ) - 1 := by zify [hp1] at h2; exact h2
    linarith
  have hneg : ∀ i, q * t ≤ i → (p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ) ≤ 0 := fun i hi ↦ by
    have hd : q ≤ i / t := (Nat.le_div_iff_mul_le ht).2 hi
    set d := i / t with hdef
    have h2 : p - 1 ≤ 2 * d := by omega
    have h3 : (p : ℤ) - 1 ≤ (2 * d : ℤ) := by zify [hp1] at h2; exact h2
    linarith
  rcases le_or_gt x (q * t) with hxq | hxq
  · exact Finset.sum_nonneg fun i hi ↦ hpos i (lt_of_lt_of_le (Finset.mem_range.1 hi) hxq)
  · have hsplit := Finset.sum_range_add_sum_Ico
      (fun i ↦ (p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) hx
    have htail : ∑ i ∈ Finset.Ico x (p * t), ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) ≤ 0 :=
      Finset.sum_nonpos fun i hi ↦ hneg i (le_trans hxq.le (Finset.mem_Ico.1 hi).1)
    linarith

/-- The signed block sum is at most `(p² − 1)t/4` on a block, attained at `x = (p−1)t/2`
([LWX, Lemma 4.1 proof]: "the maximal vertical difference over `[n_k, n_{k+1}]` is achieved
when `a = (p−1)/2`"). -/
theorem four_mul_sum_block_le (p t x : ℕ) (hodd : Odd p) (ht : 0 < t) (hx : x ≤ p * t) :
    4 * ∑ i ∈ range x, ((p : ℤ) - 1 - 2 * ((i / t : ℕ) : ℤ)) ≤ ((p ^ 2 - 1) * t : ℕ) := by
  obtain ⟨h, rfl⟩ := hodd
  -- the head sum over the nonnegative terms `i < (h + 1) t` is `t · h (h + 1)`
  have hhead : ∑ i ∈ range ((h + 1) * t), ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) =
      2 * ((t * ∑ j ∈ range (h + 1), (h - j) : ℕ) : ℤ) := by
    rw [← sum_range_mul_div t (h + 1) ht (fun j ↦ h - j), Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i / t ≤ h := by
      have : i / t < h + 1 := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact Finset.mem_range.1 hi)
      omega
    set d := i / t with hd
    rw [Nat.cast_sub hi']
    push_cast
    ring
  have hgauss : (∑ j ∈ range (h + 1), (h - j) : ℕ) * 2 = (h + 1) * h := by
    have := Finset.sum_range_reflect (fun j ↦ j) (h + 1)
    simp only [add_tsub_cancel_right] at this
    rw [this, Finset.sum_range_id_mul_two]
    rfl
  have hval : 4 * ∑ i ∈ range ((h + 1) * t), ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) =
      (((2 * h + 1) ^ 2 - 1) * t : ℕ) := by
    rw [hhead]
    have hg' : (∑ j ∈ range (h + 1), ((h - j : ℕ) : ℤ)) * 2 = ((h : ℤ) + 1) * h := by
      have := congrArg (fun n : ℕ ↦ (n : ℤ)) hgauss
      push_cast at this
      exact this
    have hsq : ((2 * h + 1) ^ 2 - 1 : ℕ) = 4 * h * (h + 1) := by
      rw [show (2 * h + 1) ^ 2 = 4 * h * (h + 1) + 1 by ring, Nat.add_sub_cancel]
    rw [hsq]
    push_cast
    linear_combination (4 * (t : ℤ)) * hg'
  -- compare the partial sum with the head sum
  have hle : ∑ i ∈ range x, ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) ≤
      ∑ i ∈ range ((h + 1) * t), ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) := by
    have hpos : ∀ i, i < (h + 1) * t → 0 ≤ ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) :=
      fun i hi ↦ by
        have hd : i / t < h + 1 := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
        set d := i / t with hdef
        have h2 : (d : ℤ) ≤ h := by exact_mod_cast Nat.lt_succ_iff.1 hd
        push_cast
        linarith
    have hneg : ∀ i, (h + 1) * t ≤ i → ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) ≤ 0 :=
      fun i hi ↦ by
        have hd : h + 1 ≤ i / t := (Nat.le_div_iff_mul_le ht).2 hi
        set d := i / t with hdef
        have h2 : (h : ℤ) + 1 ≤ (d : ℤ) := by exact_mod_cast hd
        push_cast
        linarith
    rcases le_or_gt x ((h + 1) * t) with hxq | hxq
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hxq)
        fun i hi _ ↦ hpos i (Finset.mem_range.1 hi)
    · have hsplit := Finset.sum_range_add_sum_Ico
        (fun i ↦ ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ))) hxq.le
      have htail : ∑ i ∈ Finset.Ico ((h + 1) * t) x,
          ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) ≤ 0 :=
        Finset.sum_nonpos fun i hi ↦ hneg i (Finset.mem_Ico.1 hi).1
      linarith
  calc 4 * ∑ i ∈ range x, ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ))
      ≤ 4 * ∑ i ∈ range ((h + 1) * t), ((2 * h + 1 : ℕ) - 1 - 2 * ((i / t : ℕ) : ℤ)) := by
        linarith
    _ = (((2 * h + 1) ^ 2 - 1) * t : ℕ) := hval

/-- **[LWX, Lemma 4.1]** (lower half): the lower bound polygon lies on/below the upper bound
polygon. -/
theorem two_mul_lwxLambda_le_lwxUpperTwice (p t n : ℕ) (hp : 0 < p) (ht : 0 < t) :
    2 * lwxLambda p t n ≤ lwxUpperTwice p t n := by
  have hpt : 0 < p * t := Nat.mul_pos hp ht
  have hn : touchX p t (n / (p * t)) + n % (p * t) = n := by
    rw [touchX, Nat.mul_comm (n / (p * t)) (p * t), Nat.div_add_mod]
  have hx : n % (p * t) ≤ p * t := (Nat.mod_lt n hpt).le
  have key := lwxUpperTwice_sub_two_mul_lwxLambda_eq p t (n / (p * t)) (n % (p * t)) ht hx
  have hnn := sum_block_nonneg p t (n % (p * t)) ht hx
  rw [hn] at key
  have h2 : ((2 * lwxLambda p t n : ℕ) : ℤ) ≤ (lwxUpperTwice p t n : ℕ) := by
    push_cast
    linarith
  exact_mod_cast h2

/-- **[LWX, Lemma 4.1]**: the maximal vertical difference between the lower bound polygon and
the upper bound polygon is `(p² − 1)·t/8` (in `v(T)`-units), for `p` odd. -/
theorem lwxUpperTwice_sub_two_mul_lwxLambda_le (p t n : ℕ) (hodd : Odd p) (ht : 0 < t) :
    4 * (lwxUpperTwice p t n - 2 * lwxLambda p t n) ≤ (p ^ 2 - 1) * t := by
  have hp : 0 < p := hodd.pos
  have hpt : 0 < p * t := Nat.mul_pos hp ht
  have hn : touchX p t (n / (p * t)) + n % (p * t) = n := by
    rw [touchX, Nat.mul_comm (n / (p * t)) (p * t), Nat.div_add_mod]
  have hx : n % (p * t) ≤ p * t := (Nat.mod_lt n hpt).le
  have key := lwxUpperTwice_sub_two_mul_lwxLambda_eq p t (n / (p * t)) (n % (p * t)) ht hx
  have hb := four_mul_sum_block_le p t (n % (p * t)) hodd ht hx
  rw [hn] at key
  have hle := two_mul_lwxLambda_le_lwxUpperTwice p t n hp ht
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp
  zify [hle, hp2]
  rw [key]
  push_cast [Nat.cast_sub hp2] at hb
  exact hb

/-! ### The band identities [LWX, p. 25] -/

/-- On the band `n_k − t ≤ n < n_k + t` the increment `⌊n/t⌋ − ⌊n/pt⌋` is exactly `k(p − 1)`
([LWX, §3.23 Step II]: "`⌊n_k/t⌋ − ⌊n_k/pt⌋ = kq − kq/p = kφ(q)`"). -/
theorem div_sub_div_eq_of_mem_band (p t k n : ℕ) (hp : 0 < p) (ht : 0 < t)
    (h1 : touchX p t k ≤ n + t) (h2 : n < touchX p t k + t) :
    n / t - n / (p * t) = k * (p - 1) := by
  have hpt : 0 < p * t := Nat.mul_pos hp ht
  have hkp : k ≤ k * p := Nat.le_mul_of_pos_right k hp
  rcases le_or_gt (touchX p t k) n with hn | hn
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hi : i < t := by omega
    rw [touchX_add_div p t k i ht, Nat.div_eq_of_lt hi, add_zero,
      touchX_add_div_mul p t k i hpt (lt_of_lt_of_le hi (Nat.le_mul_of_pos_left t hp)),
      Nat.mul_sub_one]
  · have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [touchX] at hn
      · exact hk
    have hkp1 : 1 ≤ k * p := Nat.mul_pos hk hp
    have hd1 : n / t = k * p - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.sub_one_mul]
        rw [touchX, ← mul_assoc] at h1
        generalize k * p * t = B at *
        omega
      · rw [Nat.sub_add_cancel hkp1]
        rw [touchX, ← mul_assoc] at hn
        exact hn
    have hd2 : n / (p * t) = k - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.sub_one_mul]
        rw [touchX] at h1
        have : t ≤ p * t := Nat.le_mul_of_pos_left t hp
        generalize k * (p * t) = B at *
        generalize p * t = C at *
        omega
      · rw [Nat.sub_add_cancel hk]
        rw [touchX] at hn
        exact hn
    rw [hd1, hd2, Nat.mul_sub_one]
    generalize k * p = A at *
    omega

/-- Right band identity: `λ(n_k + i) = λ(n_k) + k(p−1)·i` for `i ≤ t`. -/
theorem lwxLambda_touchX_add (p t k i : ℕ) (hp : 0 < p) (ht : 0 < t) (hi : i ≤ t) :
    lwxLambda p t (touchX p t k + i) = lwxLambda p t (touchX p t k) + k * (p - 1) * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, lwxLambda_succ, ih (Nat.le_of_succ_le hi),
      div_sub_div_eq_of_mem_band p t k (touchX p t k + i) hp ht (by omega) (by omega)]
    ring

/-- Left band identity: `λ(n_k − i) + k(p−1)·i = λ(n_k)` for `i ≤ t`. -/
theorem lwxLambda_touchX_sub (p t k i : ℕ) (hp : 0 < p) (ht : 0 < t) (hi : i ≤ t)
    (hik : i ≤ touchX p t k) :
    lwxLambda p t (touchX p t k - i) + k * (p - 1) * i = lwxLambda p t (touchX p t k) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hik' : i ≤ touchX p t k := by omega
    have e : touchX p t k - i = (touchX p t k - (i + 1)) + 1 := by omega
    have hband := div_sub_div_eq_of_mem_band p t k (touchX p t k - (i + 1)) hp ht (by omega)
      (by omega)
    rw [← ih (Nat.le_of_succ_le hi) hik', e, lwxLambda_succ, hband]
    ring

/-- Beyond the band on the right, `λ` exceeds the band line by at least `i − t`
([LWX, p. 25]: "equality if and only if `i ∈ [−t, t]`", quantified). -/
theorem lwxLambda_touchX_add_ge (p t k i : ℕ) (hp : 1 < p) (ht : 0 < t) (hi : t ≤ i) :
    lwxLambda p t (touchX p t k) + k * (p - 1) * i + (i - t) ≤
      lwxLambda p t (touchX p t k + i) := by
  have hp0 : 0 < p := by omega
  have hpt : 0 < p * t := Nat.mul_pos hp0 ht
  have hinc : ∀ n, touchX p t k + t ≤ n → k * (p - 1) + 1 ≤ n / t - n / (p * t) := fun n hn ↦ by
    have hmono : (touchX p t k + t) / t - (touchX p t k + t) / (p * t) ≤ n / t - n / (p * t) := by
      have h : (touchX p t k + t) / t - (touchX p t k + t) / t / p ≤ n / t - n / t / p :=
        monotone_sub_div p (Nat.div_le_div_right (c := t) hn)
      rwa [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm t p] at h
    have htp : t < p * t := by nlinarith
    have hval : (touchX p t k + t) / t - (touchX p t k + t) / (p * t) = k * (p - 1) + 1 := by
      rw [touchX_add_div p t k t ht, Nat.div_self ht, touchX_add_div_mul p t k t hpt htp,
        Nat.mul_sub_one]
      have := Nat.le_mul_of_pos_right k hp0
      generalize k * p = A at *
      omega
    rwa [hval] at hmono
  induction i, hi using Nat.le_induction with
  | base => rw [lwxLambda_touchX_add p t k t hp0 ht le_rfl, Nat.sub_self, add_zero]
  | succ i hi ih =>
    rw [← add_assoc, lwxLambda_succ, Nat.mul_succ]
    have := hinc (touchX p t k + i) (by omega)
    generalize (touchX p t k + i) / t - (touchX p t k + i) / (p * t) = c at this ⊢
    omega

/-- Beyond the band on the left, `λ` exceeds the band line by at least `i − t`. -/
theorem lwxLambda_touchX_sub_ge (p t k i : ℕ) (hp : 1 < p) (ht : 0 < t) (hi : t ≤ i)
    (hik : i ≤ touchX p t k) :
    lwxLambda p t (touchX p t k) + (i - t) ≤
      lwxLambda p t (touchX p t k - i) + k * (p - 1) * i := by
  have hp0 : 0 < p := by omega
  have hpt : 0 < p * t := Nat.mul_pos hp0 ht
  have hdec : ∀ n, n + t + 1 ≤ touchX p t k → n / t - n / (p * t) + 1 ≤ k * (p - 1) :=
    fun n hn ↦ by
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [touchX] at hn
        · exact hk
      have hkp : k ≤ k * p := Nat.le_mul_of_pos_right k hp0
      have hkp2 : 2 ≤ k * p := by nlinarith
      have hmono : n / t - n / (p * t) ≤
          (touchX p t k - t - 1) / t - (touchX p t k - t - 1) / (p * t) := by
        have h : n / t - n / t / p ≤
            (touchX p t k - t - 1) / t - (touchX p t k - t - 1) / t / p :=
          monotone_sub_div p
            (Nat.div_le_div_right (c := t) (show n ≤ touchX p t k - t - 1 by omega))
        rwa [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm t p] at h
      have e1 : (touchX p t k - t - 1) / t = k * p - 2 := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.sub_mul, touchX, ← mul_assoc]
          have : t ≤ k * p * t := Nat.le_mul_of_pos_left t (Nat.mul_pos hk hp0)
          generalize k * p * t = B at *
          omega
        · rw [show k * p - 2 + 1 = k * p - 1 by omega, Nat.sub_one_mul, touchX, ← mul_assoc]
          have : 2 * t ≤ k * p * t := Nat.mul_le_mul_right t hkp2
          generalize k * p * t = B at *
          omega
      have e2 : (touchX p t k - t - 1) / (p * t) = k - 1 := by
        rw [touchX] at hn
        apply Nat.div_eq_of_lt_le
        · rw [Nat.sub_one_mul, touchX]
          have : t + 1 ≤ p * t := by nlinarith
          generalize k * (p * t) = B at *
          generalize p * t = C at *
          omega
        · rw [Nat.sub_add_cancel hk, touchX]
          omega
      rw [e1, e2] at hmono
      have hM : 1 ≤ k * (p - 1) := Nat.mul_pos hk (by omega)
      rw [Nat.mul_sub_one] at hM ⊢
      generalize k * p = A at *
      generalize n / t - n / (p * t) = c at *
      omega
  induction i, hi using Nat.le_induction with
  | base => rw [lwxLambda_touchX_sub p t k t hp0 ht le_rfl (by omega), Nat.sub_self, add_zero]
  | succ i hi ih =>
    have hik' : i ≤ touchX p t k := by omega
    have e : touchX p t k - i = (touchX p t k - (i + 1)) + 1 := by omega
    have hd := hdec (touchX p t k - (i + 1)) (by omega)
    have ih' := ih hik'
    rw [e, lwxLambda_succ] at ih'
    rw [Nat.mul_succ]
    generalize (touchX p t k - (i + 1)) / t - (touchX p t k - (i + 1)) / (p * t) = c at hd ih'
    omega

/-- [LWX, p. 25] verbatim: `λ(n_k + i) = λ(n_k) + k(p−1)·i` **iff** `i ≤ t`. -/
theorem lwxLambda_touchX_add_eq_iff (p t k i : ℕ) (hp : 1 < p) (ht : 0 < t) :
    lwxLambda p t (touchX p t k + i) = lwxLambda p t (touchX p t k) + k * (p - 1) * i ↔
      i ≤ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ lwxLambda_touchX_add p t k i (by omega) ht h⟩
  by_contra hi
  have := lwxLambda_touchX_add_ge p t k i hp ht (by omega)
  omega

end LWX
