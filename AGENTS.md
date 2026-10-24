# Keel

Keel is a linear, effect-typed language for systems code. This repository has its compiler,
`keelc` (Haskell, in `ref/`), its specification (`spec/`), a parser written in Keel
(`ref/selfhost/`), and editor support (`editors/`).

## Writing Keel

Before writing or changing any `.kl` file, read
`editors/claude-code/skills/keel/SKILL.md` and follow it. Keel is not in your training data,
and code guessed from Haskell or OCaml almost parses. The skill covers the workflow
(`keelc check` after every definition), the mistakes agents make, with the compiler's exact
messages, and examples that the test suite runs.

## Working on the compiler

- **Run it uncommitted:** `cd ref && cabal run -v0 exe:keelc -- check|run|build FILE.kl`.
- **Tests:** `cd ref && cabal test all`. That runs the core suite, then every native case
  compared with the evaluator and checked for leaks (`live=0`), then RISC-V under QEMU. x86-64
  runs too when `KEEL_X86_HOST` names an ssh host (ask the user for it); otherwise it's skipped
  with a message. Report results as the suite prints them, skipped parts included.
- **Two parsers:** the test suite checks that `ref/selfhost/parser.kl` prints the same tree as
  `ref/src/Keel/Parser.hs` for every test file, so a syntax change goes into both.
- **Specs:** a language change also updates `spec/surface.md` (syntax) or `spec/core.md`
  (semantics). Add new mistakes agents make to the skill's table.
- **The hook reinstalls keelc:** with `git config core.hooksPath .githooks`, a commit that
  changes `ref/src`, `ref/app`, `ref/std` or the `.cabal` file reinstalls `keelc` in the
  background (`.git/keelc-install.log`). Don't run `cabal install` while
  `.git/keelc-install.lock` exists: the two would share `ref/dist-newstyle`.
