#!/bin/bash

output="$(pdflatex -shell-escape -halt-on-error "$1" | grep -A3 ^! | cat)"

if [ ! -z "${output}" ];
then
    echo -e "\n\e[31mError is:\e[0m"
    echo "${output}"
    exit 1
fi
