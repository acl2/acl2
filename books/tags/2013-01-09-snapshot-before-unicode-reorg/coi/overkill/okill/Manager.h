// Overkill System for ACL2 Testing
// Written by Jared Davis 

#ifndef INCLUDED_OVERKILL_MANAGER_H
#define INCLUDED_OVERKILL_MANAGER_H

#include <string>
#include <list>
#include <pthread.h>
using namespace std;

class Worker;

class Manager 
{
private:
    string d_cmdsFile;
    string d_hostsFile;
    string d_logFile;

    pthread_mutex_t d_mutex;
    list<string> d_workList;
    list<Worker*> d_workers;   

    Manager(const Manager& rhs);  // no copying!
    const Manager& operator=(const Manager& rhs); // no assignment!

    void parseOptions(int argc, char** argv);

public:
    Manager(int argc, char** argv);
    ~Manager();

    void startWorkers();

    bool requestWork(const Worker& requestor, string& result);

    const string& getLogFile() const;
};

#endif // INCLUDED_OVERKILL_MANAGER_H
