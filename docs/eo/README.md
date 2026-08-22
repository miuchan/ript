# Dokumentaro de Ript

[English](../en/README.md) · [简体中文](../zh-CN/README.md) ·
[日本語](../ja/README.md) · [Esperanto](README.md)

Ript estas kern-kontrolita Lean 4-esplorbiblioteko por rimed-indeksitaj
informprocezoj. Ĝi ligas ruleblan finian sintakson kun probablaj, kvantumaj,
kaŭzaj, komputaj, semantik-informaj, decidaj kaj termodinamikaj modeloj, dum
laŭvolaj kapabloj restas apartaj.

> [!IMPORTANT]
> La deponejo enhavas multe da veraj pruvoj, sed restas frufaza esploro. La
> fina tutmonda teoremo kaj stabila API ankoraŭ ne ekzistas.

## Nuna stato

- rimed-sentema sintakso, buĝetoj, valideco, relativa kompleteco kaj libera
  semantiko kompiliĝas;
- ĉiuj ses modelfamilioj havas konkretajn okazojn kaj kontrolitajn ekzemplojn;
- modeloj kaj rimedŝanĝaj morfioj formas kontrolitajn bikategoriajn tavolojn;
- interna univalento kaj complete-Segal-fundamentoj restas laŭflue de la
  rulebla kerno;
- generitaj hammock-mapspacoj ekvivalentas al la faktaj lokalizaj celoj kaj
  havas eksplicitajn nervajn homotopiajn inversojn kaj finiĝantan redukton.

La fronto estas critical-pair joinability, klasika reduced-hammock-invarianto,
norma malfort-ekvivalenta pako kaj la tutmonda Rezk-teoremo.

## Komencu ĉi tie

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
./scripts/quality-gate.sh
```

Daŭrigu per la [komenca gvidilo](GETTING_STARTED.md).

## Legu laŭ tasko

- **Kompreni:** [Amplekso kaj fido](PROJECT_SCOPE.md) · [Arkitekturo](ARCHITECTURE.md)
- **Vidi pruvojn:** [Esplora stato](RESEARCH_STATUS.md) · [Modelmatrico](reference/MODEL_MATRIX.md)
- **Auditi:** [Plano](reference/BLUEPRINT.md) · [Aksiomoj](reference/AXIOMS.md) ·
  [Konjektoj](reference/CONJECTURES.md)
- **Partopreni:** [Kontribui](CONTRIBUTING.md) · [Regado](GOVERNANCE.md) ·
  [Sekureco](SECURITY.md)
- **Ŝanĝi lingvon:** [Plurlingva dokumentara nabo](../README.md)

## Matureco kaj reuzo

Fiksu plenan commit-SHA por reprodukteblo. Ne ekzistas stabila eldono aŭ API-
garantio. Neniu malfermfonta permesilo estas elektita; publika videbleco ne
donas rajton kopii, ŝanĝi aŭ redistribui.
