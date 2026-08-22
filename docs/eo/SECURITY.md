# Sekureca politiko

[English](../en/SECURITY.md) · [简体中文](../zh-CN/SECURITY.md) ·
[日本語](../ja/SECURITY.md) · [Esperanto](SECURITY.md)

Ript estas formala esplorbiblioteko, ne gastigita servo. Sekureco ampleksas
pruvan fidon, ruleblajn ekzemplojn, dependecon kaj CI-integron, kaj nesekuran
konduton kiu povus damaĝi uzantojn.

## Subteno

Nur la nuna `main` estas subtenata. Raporto devas nomi la plenan commit-SHA kaj
la fiksitan Lean-ilĉenon; ne ekzistas retroporta politiko.

## Privata raportado

Uzu privatan vundeblan raportadon en la GitHub **Security**-langeto se ĝi
disponeblas. Alie malfermu nur minimuman publikan peton por privata kanalo; ne
publikigu ekspluaton, akreditaĵojn aŭ privatajn datumojn.

Inkludu modulon kaj commit, efikon, realisman minacon, minimuman reprodukton,
trafitan fidolimon kaj konatan mildigon.

## Amplekso kaj respondo

Fid-evitoj, kaŝitaj aksiomoj, unsafe-deklaroj, kontrolpordaj preteriroj,
atingeblaj dependeco/CI-kompromisoj, ruleblaj limrompoj kaj sekreta elfluo estas
sekurecaj. Registrita konjekto, modela malkonsento aŭ malstabila API ordinare ne
estas. Respondo estas laŭeble sen SLA; korekto devas pasi la normalajn kernajn,
auditajn kaj CI-kontrolojn. Vidu la [radikan politikon](../../SECURITY.md).
