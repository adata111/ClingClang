#!/bin/bash

# Goes through each rkt file, and generates the result of the racket expression
# Considers the cases where the rkt files needs input from a .in file

for f in ./var_*.rkt
do
    f="${f%.rkt}"
    echo "$f"


    if [ -f "$f.in" ]; 
    then
        racket -e "`cat $f.rkt`" < "$f.in" > "$f.res"
    else
        racket -e "`cat $f.rkt`" > "$f.res"
    fi
done