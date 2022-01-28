#!/bin/sh

for file in `ls ./*.sl`;
do
    echo $file
    sailc $file
done
