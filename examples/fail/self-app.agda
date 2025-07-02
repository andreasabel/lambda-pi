Bot : Set1
Bot = (A : Set) → A

omega : Bot → Bot
omega = λ x → x Bot x

-- should fail with level error
