def belowZero (l : List Int) : Bool :=
  go 0 l
where
  go (cur : Int) (remaining : List Int) : Bool :=
    if cur < 0 then
      true
    else
      match remaining with
      | [] => false
      | l::rem => go (cur + l) rem

theorem belowZero_iff {l : List Int} : belowZero l ↔ ∃ n, (l.take n).sum < 0 := by
  suffices ∀ c, belowZero.go c l ↔ ∃ n, c + (l.take n).sum < 0 by simpa using this 0
  intro c
  induction l generalizing c with
  | nil => simp [belowZero.go]
  | cons h t ih =>
    simp only [belowZero.go, Bool.if_true_left, Bool.or_eq_true, decide_eq_true_eq, ih]
    refine ⟨?_, ?_⟩
    · rintro (hc|⟨n, hn⟩)
      · exact ⟨0, by simpa⟩
      · exact ⟨n + 1, by simpa [← Int.add_assoc]⟩
    · rintro ⟨n, hn⟩
      rcases n with (_|n)
      · exact Or.inl (by simpa using hn)
      · exact Or.inr ⟨n, by simpa [Int.add_assoc] using hn⟩

/-!
## Prompt

```python3
from typing import List


def below_zero(operations: List[int]) -> bool:
    """ You're given a list of deposit and withdrawal operations on a bank account that starts with
    zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
    at that point function should return True. Otherwise it should return False.
    >>> below_zero([1, 2, 3])
    False
    >>> below_zero([1, 2, -4, 5])
    True
    """
```

## Canonical solution

```python3
    balance = 0

    for op in operations:
        balance += op
        if balance < 0:
            return True

    return False
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == False
    assert candidate([1, 2, -3, 1, 2, -3]) == False
    assert candidate([1, 2, -4, 5, 6]) == True
    assert candidate([1, -1, 2, -2, 5, -5, 4, -4]) == False
    assert candidate([1, -1, 2, -2, 5, -5, 4, -5]) == True
    assert candidate([1, -2, 2, -2, 5, -5, 4, -4]) == True
```
-/
