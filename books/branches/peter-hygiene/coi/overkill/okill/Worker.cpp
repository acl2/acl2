// Overkill System for ACL2 Testing
// Written by Jared Davis 

#include "Worker.h"
#include "Manager.h"
#include <iostream>
#include <fstream>
#include <cassert>
#include <cstdlib>


Worker::Worker(Manager& manager, const string& hostName)
    : d_manager(manager), 
      d_hostName(hostName)
{

}

pthread_t Worker::getPid() const
{
    return d_pid;
}

void Worker::startWork()
{
    pthread_create(&d_pid, NULL, Worker::threadStarter, (void*)this);
}

void* Worker::threadStarter(void* worker) 
{
    ((Worker*)worker)->doWork();
    return NULL;
}

void Worker::doWork()
{
    string work;
    while(d_manager.requestWork(*this, work))
    {	
	// BZO use ssh instead?
	string cmd = "rsh " + d_hostName + " " + work;
	cout << "[" << d_hostName << "]: " << work << endl;
	system(cmd.c_str());
    }

    cout << "[" << d_hostName << "]: out of work" << endl;

    ofstream out;
    out.open(d_manager.getLogFile().c_str(), ofstream::out | ofstream::app);
    out << "Goodbye (" << d_hostName << ")" << endl;
    out.close();
}

