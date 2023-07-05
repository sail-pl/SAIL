import test_utils
// Parallel branches doing nothing

process Main {
Init:
Loop:

    {
        {

        }
        ||
        {   

        }
    };
    exit(0);
}