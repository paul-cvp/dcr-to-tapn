from django.test.testcases import TestCase

from src.jobs.job_creator import generate, generate_labelling, update
from src.jobs.models import JobTypes, Job
from src.jobs.tasks import prediction_task
from src.utils.django_orm import duplicate_orm_row
from src.utils.tests_utils import create_test_job


class TestJobCreator(TestCase):
    def test_generate(self):
        job = create_test_job()

        initial_job = job.to_dict()
        del initial_job['id']
        del initial_job['created_date']
        del initial_job['modified_date']
        del initial_job['hyperparameter_optimizer']
        del initial_job['encoding']['features']
        del initial_job['labelling']['attribute_name']

        generated_job = generate(split=job.split, payload={
            'type': 'classification',
            'split_id': 1,
            'config': {
                'clusterings': ['noCluster'],
                'encodings': ['simpleIndex'],
                'encoding': {
                    'padding': False,
                    'prefix_length': 1,
                    'generation_type': 'only',
                    'add_remaining_time': False,
                    'add_elapsed_time': False,
                    'add_executed_events': False,
                    'add_resources_used': False,
                    'add_new_traces': False,
                    'features': [],
                },
                'create_models': False,
                'methods': ['randomForest'],
                'kmeans': {},
                'incremental_train': {
                    'base_model': None,
                },
                'hyperparameter_optimizer': {
                    'algorithm_type': 'tpe',
                    'max_evaluations': 10,
                    'performance_metric': 'rmse',
                    'type': 'none',
                },
                'labelling': {
                    'type': 'next_activity',
                    'attribute_name': '',
                    'threshold_type': 'threshold_mean',
                    'threshold': 0,
                },
                'classification.decisionTree': {},
                'classification.knn': {},
                'classification.randomForest': {},
                'classification.adaptiveTree': {},
                'classification.hoeffdingTree': {},
                'classification.multinomialNB': {},
                'classification.perceptron': {},
                'classification.SGDClassifier': {},
                'classification.xgboost': {},
                'classification.nn': {},
                'regression.lasso': {},
                'regression.linear': {},
                'regression.randomForest': {},
                'regression.xgboost': {},
                'regression.nn': {},
                'time_series_prediction.rnn': {}
            }
        })[0].to_dict()
        del generated_job['id']
        del generated_job['created_date']
        del generated_job['modified_date']
        del generated_job['hyperparameter_optimizer']
        del generated_job['encoding']['features']
        del generated_job['labelling']['attribute_name']

        self.assertDictEqual(initial_job, generated_job)

    def test_generate_up_to(self):
        job = create_test_job()

        initial_job = job.to_dict()
        del initial_job['id']
        del initial_job['created_date']
        del initial_job['modified_date']
        del initial_job['hyperparameter_optimizer']
        del initial_job['encoding']['features']
        del initial_job['encoding']['task_generation_type']
        del initial_job['labelling']['attribute_name']

        generated_job = generate(split=job.split, payload={
            'type': 'classification',
            'split_id': 1,
            'config': {
                'clusterings': ['noCluster'],
                'encodings': ['simpleIndex'],
                'encoding': {
                    'padding': False,
                    'prefix_length': 2,
                    'generation_type': 'up_to',
                    'add_remaining_time': False,
                    'add_elapsed_time': False,
                    'add_executed_events': False,
                    'add_resources_used': False,
                    'add_new_traces': False,
                    'features': [],
                },
                'create_models': False,
                'methods': ['randomForest'],
                'kmeans': {},
                'incremental_train': {
                    'base_model': None,
                },
                'hyperparameter_optimizer': {
                    'algorithm_type': 'tpe',
                    'max_evaluations': 10,
                    'performance_metric': 'rmse',
                    'type': 'none',
                },
                'labelling': {
                    'type': 'next_activity',
                    'attribute_name': '',
                    'threshold_type': 'threshold_mean',
                    'threshold': 0,
                },
                'classification.decisionTree': {},
                'classification.knn': {},
                'classification.randomForest': {},
                'classification.adaptiveTree': {},
                'classification.hoeffdingTree': {},
                'classification.multinomialNB': {},
                'classification.perceptron': {},
                'classification.SGDClassifier': {},
                'classification.xgboost': {},
                'classification.nn': {},
                'regression.lasso': {},
                'regression.linear': {},
                'regression.randomForest': {},
                'regression.xgboost': {},
                'regression.nn': {},
                'time_series_prediction.rnn': {}
            }
        })[0].to_dict()
        del generated_job['id']
        del generated_job['created_date']
        del generated_job['modified_date']
        del generated_job['hyperparameter_optimizer']
        del generated_job['encoding']['features']
        del generated_job['encoding']['task_generation_type']
        del generated_job['labelling']['attribute_name']

        self.assertDictEqual(initial_job, generated_job)

    def test_generate_labelling(self):
        job = create_test_job()
        job.type = JobTypes.LABELLING.value
        job.save()

        generated_job = generate_labelling(split=job.split, payload={
            'type': 'labelling',
            'split_id': 1,
            'config': {
                'encodings': ['simpleIndex'],
                'encoding': {
                    'padding': False,
                    'prefix_length': 1,
                    'generation_type': 'only',
                    'add_remaining_time': False,
                    'add_elapsed_time': False,
                    'add_executed_events': False,
                    'add_resources_used': False,
                    'add_new_traces': False,
                    'features': [],
                },
                'create_models': False,
                'labelling': {
                    'type': 'next_activity',
                    'attribute_name': '',
                    'threshold_type': 'threshold_mean',
                    'threshold': 0,
                }
            }
        })[0]

        self.assertEqual(job.type, generated_job.type)
        self.assertEqual(job.split, generated_job.split)

        job.encoding.features = None
        generated_job.encoding.features = None
        self.assertDictEqual(job.encoding.to_dict(), generated_job.encoding.to_dict())

        job.labelling.attribute_name = None
        generated_job.labelling.attribute_name = None
        self.assertDictEqual(job.labelling.to_dict(), generated_job.labelling.to_dict())

    def test_generate_labelling_up_to(self):
        job = create_test_job()
        job.type = JobTypes.LABELLING.value
        job.save()

        generated_job = generate_labelling(split=job.split, payload={
            'type': 'labelling',
            'split_id': 1,
            'config': {
                'encodings': ['simpleIndex'],
                'encoding': {
                    'padding': False,
                    'prefix_length': 2,
                    'generation_type': 'up_to',
                    'add_remaining_time': False,
                    'add_elapsed_time': False,
                    'add_executed_events': False,
                    'add_resources_used': False,
                    'add_new_traces': False,
                    'features': [],
                },
                'create_models': False,
                'labelling': {
                    'type': 'next_activity',
                    'attribute_name': '',
                    'threshold_type': 'threshold_mean',
                    'threshold': 0,
                }
            }
        })[0]

        self.assertEqual(job.type, generated_job.type)
        self.assertEqual(job.split, generated_job.split)

        job.encoding.features = None
        job.encoding.task_generation_type = None
        generated_job.encoding.features = None
        generated_job.encoding.task_generation_type = None
        self.assertDictEqual(job.encoding.to_dict(), generated_job.encoding.to_dict())

        job.labelling.attribute_name = None
        generated_job.labelling.attribute_name = None
        self.assertDictEqual(job.labelling.to_dict(), generated_job.labelling.to_dict())

    def test_update(self):
        job = create_test_job()
        prediction_task(job.id)

        # job2 = duplicate_orm_row(job) #todo: replace with simple CREATE
        job2 = Job.objects.create(
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
        job.refresh_from_db()
        job2.incremental_train = job
        job2.type = JobTypes.UPDATE.value
        job2.save()

        initial_job = job2#.to_dict()

        generated_job = update(split=job.split, payload={
            'type': 'classification',
            'split_id': 1,
            'config': {
                'clusterings': ['noCluster'],
                'encodings': ['simpleIndex'],
                'encoding': {
                    'padding': False,
                    'prefix_length': 1,
                    'generation_type': 'only',
                    'add_remaining_time': False,
                    'add_elapsed_time': False,
                    'add_executed_events': False,
                    'add_resources_used': False,
                    'add_new_traces': False,
                    'features': [],
                },
                'create_models': False,
                'methods': ['randomForest'],
                'kmeans': {},
                'incremental_train': [job.id],
                'hyperparameter_optimizer': {
                    'algorithm_type': 'tpe',
                    'max_evaluations': 10,
                    'performance_metric': 'rmse',
                    'type': 'none',
                },
                'labelling': {
                    'type': 'next_activity',
                    'attribute_name': '',
                    'threshold_type': 'threshold_mean',
                    'threshold': 0,
                }
            }
        })[0]#.to_dict()

        #TODO: probably missing to_dict for incremental model
        # self.assertEqual(initial_job, generated_job)
