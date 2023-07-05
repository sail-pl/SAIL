#! /bin/bash

cd sailor.t
echo "" > run.t
#echo "  $ sailor print_utils.sl -m lib" >> run.t
for f in *.sl ; do if [ "$f" != "test_utils.sl" ]; then echo "  $ sailor ${f} && ./${f%.*}" >> run.t; fi; done

