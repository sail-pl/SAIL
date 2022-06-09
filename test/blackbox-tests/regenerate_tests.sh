#! /bin/bash

cd saili.t
echo "" > run.t
for f in *.sl ; do echo "  $ saili ${f}" >> run.t; done

cd ../sailor.t
echo "" > run.t
for f in *.sl ; do echo "  $ sailor ${f} --run" >> run.t; done

