/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n ^ 2 ≥ 2 ^ 2 := by rel [hn]
    _ > 2 := by numbers

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hx1 | hx2 := h2
  left
  calc
    x = 1 := by addarith [hx1]
    _ = 1 := by numbers
  right
  calc
    x = 2 := by addarith [hx2]

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hp | hn := h
  calc
    x ^ 2 + 1 = 4 ^ 2 + 1 := by rw [hp]
    _ = 17 := by ring
  calc
    x ^ 2 + 1 = (-4) ^ 2 + 1 := by rw [hn]
    _ = 17 := by ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  calc
    x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw [h1]
    _ = 0 := by ring
  calc
    x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw [h2]
    _ = 0 := by ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  sorry

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = 3 - t + t := by rw [h]
    _ = 3 := by ring

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc
    b < -a / 2 := by addarith [h]

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    x = (y - 1) / 2 := by addarith [h]
    _ = y / 2 - 1 / 2 := by ring
    _ < y / 2 - 1 / 2 + 1 / 2 := by extra
    _ = y / 2 := by ring

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h :=
  calc
    (x + 3) * (x - 1) = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := by rw [hx]
  have h' := eq_zero_or_eq_zero_of_mul_eq_zero h
  obtain hm3 | h1 := h'
  left
  calc
    x = x + 3 - 3 := by ring
    _ = 0 - 3 := by rw [hm3]
    _ = -3 := by numbers
  right
  calc
    x = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h1]
    _ = 1 := by numbers

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h :=
  calc
    t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
    _ = t ^ 2 - t ^ 2 := by rw [ht]
    _ = 0 := by ring
  have h' := eq_zero_or_eq_zero_of_mul_eq_zero h
  obtain h0 | h1 := h'
  right
  cancel 2 at h0
  left
  calc
    t = t - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h1]
    _ = 1 := by numbers

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

example {x : ℤ} : 2 * x ≠ 3 := by
  sorry

example {t : ℤ} : 5 * t ≠ 18 := by
  have h := le_or_succ_le t 3
  obtain h3 | h4 := h
  apply ne_of_lt
  calc
    5 * t ≤ 5 * 3 := by rel [h3]
    _ < 18 := by numbers
  apply ne_of_gt
  calc
    5 * t ≥ 5 * 4 := by rel [h4]
    _ > 18 := by numbers

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have h := le_or_succ_le m 5
  obtain h5 | h6 := h
  apply ne_of_lt
  calc
    m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel [h5]
    _ = 45 := by ring
    _ < 46 := by numbers
  apply ne_of_gt
  calc
    m ^ 2 + 4 * m ≥ 6 ^ 2 + 4 * 6 := by rel [h6]
    _ = 60 := by ring
    _ > 46 := by numbers
