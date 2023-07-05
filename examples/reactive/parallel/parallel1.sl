import test_utils
process Main {
Init:
Loop:

    {
        {
            signal s1;
            signal s2;
            signal s3;
            watching s2 {emit s2;when s3 {}}
            emit s1
        }
        ||
        {
            signal t1;
            signal t2;
            signal t3;
            watching t2 {emit t2; when t3{}};
            emit t2
        }
    };
    exit(0);
}