#!/bin/sh

for file in `ls ./*.sl`;
do
    echo $file
    ../_build/default/bin/sail.exe $file
done