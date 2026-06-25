# Garde le dossier rapport/ propre (regle projet : <=10 entrees/dossier).
# Tous les artefacts de compilation (.aux .log .toc .out .fls .fdb_latexmk)
# sont rediriges dans build/ ; seul main.pdf (livrable versionne) reste a la
# racine du rapport. MiKTeX recoit -aux-directory=build via latexmk.
$pdf_mode  = 1;
$aux_dir   = 'build';
