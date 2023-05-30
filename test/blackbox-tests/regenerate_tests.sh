#! /bin/bash

cd saili.t
echo "" > run.t
for f in *.sl ; do echo "  $ saili ${f}" >> run.t; done

cd ../sailor.t
echo "" > run.t
#echo "  $ sailor print_utils.sl -m lib" >> run.t
for f in *.sl ; do if [ "$f" != "print_utils.sl" ]; then echo "  $ sailor ${f} && ./${f%.*}" >> run.t; fi; done

