#ifndef INCLUDED_OVERKILL_WORKER_H
#define INCLUDED_OVERKILL_WORKER_H

#include <string>
#include <pthread.h>
using namespace std;

class Manager;

class Worker 
{
private:
    Manager& d_manager;
    const string d_hostName;
    pthread_t d_pid;

    // private copy constructor and assignment operators with no bodies 
    // do not implement these -- no copying allowed!
    Worker(const Worker& rhs);
    const Worker& operator=(const Worker& rhs);    

    static void* threadStarter(void* worker);
    void doWork();

public:
    Worker(Manager& manager, const string& hostName);	
    void startWork();

    pthread_t getPid() const;
};


#endif // INCLUDED_OVERKILL_WORKER_H
