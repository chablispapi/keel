# Keel

Keel is a linear, effect-typed functional language for systems code: kernels, firmware,
drivers. It compiles straight to native code (AArch64, x86-64, RISC-V) with no garbage
collector and no heavy runtime.

```
-- Print two squares, then return their sum.

def square : i64 ->{Panic} i64 = \n. n * n

main = out(square 3); out(square 4); square 3 + square 4
```

## Layout

- `ref/`: the compiler `keelc` (Haskell), its standard library (`ref/std`), tests and
  examples (`ref/examples`), and a parser written in Keel (`ref/selfhost`)
- `spec/`: the language specification, with syntax in `surface.md` and semantics in `core.md`
- `editors/`: a tree-sitter grammar and a Claude Code plugin (language server and skill)
- `notes.md`: the design notes Keel started from

## Build and run

You need GHC and cabal.

```
cd ref
cabal run -v0 exe:keelc -- run examples/hello.kl
cabal install exe:keelc        # puts keelc on your PATH
```

```
keelc new NAME
keelc (check | run | asm | qemu) [FILE.kl]
keelc build [FILE.kl] [-o OUT] [--target native|riscv64|x86_64] [-g]
keelc lsp
```

Without `FILE.kl`, keelc uses the `keel.project` in the current directory. Native builds use the
system `cc`. The RISC-V target also needs LLVM clang, `ld.lld` and QEMU
(`brew install llvm lld qemu`).

## Tests

```
cd ref && cabal test all
```

The suite runs the core tests, then compiles every native case and checks it against the
evaluator for both output and leaks, then runs RISC-V under QEMU. To include x86-64, set
`KEEL_X86_HOST` to an ssh host.

## License

MIT
