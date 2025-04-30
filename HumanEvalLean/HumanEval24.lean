def largest_divisor : Unit :=
  ()

/-!
## Prompt

```python3


def largest_divisor(n: int) -> int:
    """ For a given number n, find the largest number that divides n evenly, smaller than n
    >>> largest_divisor(15)
    5
    """
```

## Canonical solution

```python3
    for i in reversed(range(n)):
        if n % i == 0:
            return i
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3) == 1
    assert candidate(7) == 1
    assert candidate(10) == 5
    assert candidate(100) == 50
    assert candidate(49) == 7
```
-/