from django.test.testcases import TestCase
from rest_framework.test import APIClient

from src.jobs.models import Job
from src.jobs.tasks import prediction_task
from src.logs.log_service import get_log
from src.runtime.tasks import runtime_task, replay_task, replay_prediction_task
from src.split.models import SplitTypes, SplitOrderingMethods
from src.utils.django_orm import duplicate_orm_row
from src.utils.tests_utils import create_test_job, create_test_split, create_test_log


class TestRuntime(TestCase):

    def test_replay(self):

        job = create_test_job()
        # runtime_job = duplicate_orm_row(job)  #todo: replace with simple CREATE
        runtime_job = Job.objects.create(
            created_date=job.created_date,
            modified_date=job.modified_date,
            error=job.error,
            status=job.status,
            type=job.type,
            create_models=job.create_models,
            case_id=job.case_id,
            event_number=job.event_number,
            gold_value=job.gold_value,
            results=job.results,
            parent_job=job.parent_job,
            split=job.split,
            encoding=job.encoding,
            labelling=job.labelling,
            clustering=job.clustering,
            predictive_model=job.predictive_model,
            evaluation=job.evaluation,
            hyperparameter_optimizer=job.hyperparameter_optimizer,
            incremental_train=job.incremental_train
        )

        runtime_log = create_test_log(log_name='runtime_example.xes',
                                      log_path='cache/log_cache/test_logs/runtime_test.xes')
        runtime_job.split = create_test_split(split_type=SplitTypes.SPLIT_DOUBLE.value,
                                              split_ordering_method=SplitOrderingMethods.SPLIT_SEQUENTIAL.value,
                                              train_log=runtime_log,
                                              test_log=runtime_log)

        requests = replay_task(runtime_job, job)
        self.assertEqual(len(requests), 6)

    def test_create_replay(self):
        job = create_test_job()
        split = create_test_split()
        client = APIClient()
        response = client.post('/runtime/replay/', {
            'jobId': job.id,
            'splitId': split.id,
            }, format='json')

        self.assertEqual(201, response.status_code)

    def test_create_runtime(self):
        job = create_test_job()
        split = create_test_split()
        client = APIClient()
        response = client.post('/runtime/prediction/', {
            'jobId': job.id,
            'splitId': split.id,
            }, format='json')

        self.assertEqual(201, response.status_code)

    def test_runtime(self):
        job = create_test_job(create_models=True)
        runtime_log = create_test_log(log_name='runtime_example.xes',
                                      log_path='cache/log_cache/test_logs/runtime_test.xes')

        prediction_task(job.id)
        job.refresh_from_db()
        job.split = create_test_split(split_type=SplitTypes.SPLIT_DOUBLE.value,
                                      split_ordering_method=SplitOrderingMethods.SPLIT_SEQUENTIAL.value,
                                      train_log=runtime_log,
                                      test_log=runtime_log)

        runtime_task(job)

    def test_replay_prediction(self):
        job = create_test_job(create_models=True)
        runtime_log = create_test_log(log_name='runtime_example.xes',
                                      log_path='cache/log_cache/test_logs/runtime_test.xes')
        log = get_log(runtime_log)
        prediction_task(job.id)
        job.refresh_from_db()

        replay_prediction_task(job, job, log)
