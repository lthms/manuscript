#!/usr/bin/sh

function clone () {
    dir="${1}"
    cwd="${2}"
    tag="${3}"

    cd "${dir}"

    git clone "${cwd}" .
    git checkout "${tag}"

    cd "${cwd}"
}

function diff () {
    dir="${1}"
    tag="${2}"
    target="diff-${tag}"

    latexdiff --flatten "${dir}/main.tex" "./main.tex"  --exclude-textcmd="section,subsection,chapter" > "${target}.tex"

    pdflatex "${target}.tex"
    bibtex "${target}"
    pdflatex "${target}.tex"
    pdflatex "${target}.tex"

    rm -f $(ls ${target}* | grep -v pdf)

}

TMP_DIR="$(mktemp --directory)"
TAG="${1}"

clone "${TMP_DIR}" "$(pwd)" "${TAG}"
diff "${TMP_DIR}" "${TAG}"

rm -rf "${TMP_DIR}"
