# LOGRAC

agda

| keywords | mach |
|----------|------|
| C-c C-l | reload |
| C-c C-c | pattern-matching |
| C-c C-space | fill hole |
| C-c C-n | normalise (eval the expr) |
| C-c C-. | show ctx and normalized goal in the hole |
| C-c C-r | ko maš napisan izraz ti pol zmanjša hole --- parial proof search |
| C-c C-a | auto proof search in hole |
| C-c C-f/b | next/prev hole |

```
x y p with f x y p
... | a = ?

## strategija

- pattern match vse (smiselne) argumente
- poglej ctx ki vsebuje normaliziran cilj