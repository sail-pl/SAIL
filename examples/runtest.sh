#!/bin/sh

for file in `ls ./*.sl`;
do
    echo $file
    sailc $file >> $file.output.old
    if [ -e $file.output ] 
    then 
        diff $file.output.old $file.output
        rm $file.output.old
    else 
        mv $file.output.old $file.output

    fi
done
