#!/usr/bin/env bash

# Compile a .lagda.md file to a PDF
# (based on pandoc + agda LaTeX backend)

DOC_BASE_NAME=report
DOC_SUBDIR=report/
ALSO_COPY="src/ .agda-lib _build/"


TMP=$(mktemp -d)
echo "[BUILD] Copying files to ${TMP}"

CWD=$(pwd)

cp -r ${DOC_SUBDIR} ${ALSO_COPY} ${TMP}
cd ${TMP}

echo "[BUILD] Converting document to LaTeX (with pandoc + custom filter)"

cd ${DOC_SUBDIR}
pandoc --standalone -F pandoc-crossref --citeproc \
    --lua-filter translate-agda-blocks.lua \
    --lua-filter hidden-divs.lua \
    ${DOC_BASE_NAME}.lagda.md -o ${DOC_BASE_NAME}.lagda.tex
rm ${DOC_BASE_NAME}.lagda.md

echo "[BUILD] Formatting code blocks (with agda)"

cd ${TMP}
agda --latex --only-scope-checking --latex-dir=${DOC_SUBDIR} ${DOC_SUBDIR}${DOC_BASE_NAME}.lagda.tex

echo "[BUILD] Calling LaTeX engine"

cd ${DOC_SUBDIR}
latexmk -lualatex --interaction=batchmode ${DOC_BASE_NAME}.tex || \
    (echo "[BUILD] There was a LaTeX error, log:"; cat "${DOC_BASE_NAME}.log"; exit 1)

echo "[BUILD] Potentially broken Unicode characters:"
cat ${DOC_BASE_NAME}.log | grep "Missing character: There is no" || echo "No missing characters!"

echo "[BUILD] Copying back output"

cp ${DOC_BASE_NAME}.pdf ${CWD}

echo "[BUILD] Done"
