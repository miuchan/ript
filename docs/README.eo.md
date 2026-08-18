# Ript

**Kern-kontrolita Lean 4-fundamento por rimed-indicitaj procezteorioj.**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![Esplora stato](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript formaligas tipizitajn procezojn, kies konduto kaj rimeduzo kunmetiĝas. Ĝi
ligas plenumeblajn finiajn modelojn al kern-kontrolitaj rezultoj pri rimedlimoj,
solideco, kompleteco kaj struktur-konserva semantiko.

> [!IMPORTANT]
> Ript estas frustadia esplora programaro. La kompilitaj rezultoj estas
> kern-kontrolitaj; la publika API kaj la esplora fronto ankoraŭ evoluas.

## Rapida komenco

Instalu [elan](https://github.com/leanprover/elan), poste konstruu la projekton
kun ĝiaj fiksitaj versioj de Lean kaj Mathlib:

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

Por postuloj, plenumeblaj ekzemploj, dependaĵa uzo, reproduktebleco kaj
problemo-solvado, sekvu la [komencan gvidilon](GETTING_STARTED.md).

## Trovu tion, kion vi bezonas

- **Kio estas realigita?** Vidu la [matricon de modelkapabloj](../MODEL_MATRIX.md).
- **Kio estas pruvita aŭ ankoraŭ malferma?** Vidu la
  [esploran staton](RESEARCH_STATUS.md).
- **Kiel la biblioteko estas organizita?** Legu la
  [arkitekturan gvidilon](ARCHITECTURE.md).
- **Kiuj estas la fidaj kaj maturecaj limoj?** Legu
  [projektan amplekson kaj fidon](PROJECT_SCOPE.md).
- **Kie estas la precizaj esplorregistroj?** Uzu la
  [formalan planon](../BLUEPRINT.md), [aksioman inventaron](../AXIOMS.md) kaj
  [registron de konjektoj](../CONJECTURES.md).
- **Ĉu vi ne certas, kie komenci?** Malfermu la
  [dokumentaran centron](README.md).

## Kontribuado

Legu la [kontribuan gvidilon](../CONTRIBUTING.md) kaj rulu
`./scripts/quality-gate.sh` antaŭ ol malfermi tirpeton.

Ript estas konstruita per [Lean 4](https://lean-lang.org/) kaj
[Mathlib](https://github.com/leanprover-community/mathlib4).
